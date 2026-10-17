// Portable probe for MACHINE_CLEARS.SMC-style counters around a minimal self-modifying-code loop.
//
// Backends (no kernel driver is built, bundled or test-signed by this repository):
//   Linux   perf_event_open, per-thread, user mode only (Intel and AMD).  No driver; may need
//           kernel.perf_event_paranoid <= 2 or root.  Not available in most virtual machines.
//   Windows PawnIO (signed driver, official signed modules), AMD only: the module allows PerfEvtSel0 / PerfCtr0.
//           Intel PMU MSRs are not permitted by any stock PawnIO module, so Intel/Windows runs timing only.
//   other   timing only.
// Output is measurement evidence about one machine, never proof; see lean/PLATFORM_CONTRACT.md.
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <memory>
#include <string>
#include <vector>

#if defined(_M_X64) || defined(__x86_64__)
#define SMC_X64 1
#else
#define SMC_X64 0
#endif

#ifdef _WIN32
#define NOMINMAX
#include <windows.h>
#include <intrin.h>
#else
#include <sys/mman.h>
#include <unistd.h>
#if SMC_X64
#include <cpuid.h>
#endif
#ifdef __linux__
#include <fcntl.h>
#include <linux/perf_event.h>
#include <sched.h>
#include <sys/ioctl.h>
#include <sys/syscall.h>
#include <cerrno>
#include <fstream>
#endif
#endif

namespace {

struct Cpu {
  std::string vendor;
  unsigned family = 0, model = 0, stepping = 0;
  bool hypervisor = false;
};

Cpu cpuInfo() {
  Cpu c;
#if SMC_X64
  unsigned a = 0, b = 0, cc = 0, d = 0;
  char v[13];
#ifdef _WIN32
  int r[4];
  __cpuid(r, 0); b = r[1]; cc = r[2]; d = r[3];
  memcpy(v, &b, 4); memcpy(v + 4, &d, 4); memcpy(v + 8, &cc, 4); v[12] = 0; c.vendor = v;
  __cpuid(r, 1); a = r[0]; cc = r[2];
#else
  __get_cpuid(0, &a, &b, &cc, &d);
  memcpy(v, &b, 4); memcpy(v + 4, &d, 4); memcpy(v + 8, &cc, 4); v[12] = 0; c.vendor = v;
  __get_cpuid(1, &a, &b, &cc, &d);
#endif
  unsigned bf = (a >> 8) & 0xF;
  c.family = bf; c.model = (a >> 4) & 0xF; c.stepping = a & 0xF;
  if (bf == 0xF) c.family += (a >> 20) & 0xFF;
  if (bf == 0xF || bf == 0x6) c.model += ((a >> 16) & 0xF) << 4;
  c.hypervisor = (cc >> 31) & 1;
#endif
  return c;
}

struct Counter {
  virtual ~Counter() {}
  virtual bool start() = 0;
  virtual bool stop(uint64_t& v) = 0;
  virtual std::string name() const = 0;
};

// Event selection: raw x86 PMU encoding event[7:0] | umask << 8 | event[11:8] << 32 (AMD).
struct EventChoice { uint64_t cfg = 0; bool have = false; std::string why; };

EventChoice chooseEvent(const Cpu& c, long long override_) {
  EventChoice e;
  if (override_ >= 0) { e.cfg = (uint64_t)override_; e.have = true; e.why = "user supplied --event"; return e; }
  if (c.vendor == "GenuineIntel") {
    // Intel SDM Vol. 3B event table: MACHINE_CLEARS.SMC = event C3H, umask 04H.
    e.cfg = 0x04C3; e.have = true; e.why = "Intel MACHINE_CLEARS.SMC (C3H/04H)"; return e;
  }
  if (c.vendor == "AuthenticAMD") {
    if (c.family == 0x10 || c.family == 0x15) {
      // BKDG 31116 / 42301: EventSelect 021h "Pipeline Restart Due to Self-Modifying Code".
      e.cfg = 0x0021; e.have = true; e.why = "AMD PMCx021 pipeline restart due to SMC (Family 10h/15h BKDG)"; return e;
    }
    e.why = "no verified SMC event for AMD family " + std::to_string(c.family) +
            "h in this repository; pass --event RAW (0x0461 is l2_request_g2.smc_inval in the Linux Zen3 table: an L2 SMC-invalidation proxy, not a pipeline restart)";
    return e;
  }
  e.why = "unknown CPU vendor";
  return e;
}

#if defined(__linux__) && SMC_X64
struct PerfCounter : Counter {
  int fd = -1;
  std::string label;
  ~PerfCounter() override { if (fd >= 0) close(fd); }
  bool start() override { return ioctl(fd, PERF_EVENT_IOC_RESET, 0) == 0 && ioctl(fd, PERF_EVENT_IOC_ENABLE, 0) == 0; }
  bool stop(uint64_t& v) override {
    ioctl(fd, PERF_EVENT_IOC_DISABLE, 0);
    return read(fd, &v, sizeof v) == (ssize_t)sizeof v;
  }
  std::string name() const override { return label; }
};

std::string slurp(const char* p) {
  std::ifstream f(p);
  std::string s;
  std::getline(f, s);
  return s;
}

std::unique_ptr<Counter> openCounter(uint64_t cfg, std::string& why) {
  uint32_t type = PERF_TYPE_RAW;
  std::string t = slurp("/sys/bus/event_source/devices/cpu_core/type");  // hybrid Intel: raw events live on cpu_core
  std::string cpus = slurp("/sys/bus/event_source/devices/cpu_core/cpus");
  if (!t.empty()) {
    type = (uint32_t)atoi(t.c_str());
    int cpu = atoi(cpus.c_str());
    cpu_set_t set;
    CPU_ZERO(&set);
    CPU_SET(cpu, &set);
    sched_setaffinity(0, sizeof set, &set);  // keep the thread on a P-core, where the event exists
  }
  perf_event_attr a;
  memset(&a, 0, sizeof a);
  a.type = type; a.size = sizeof a; a.config = cfg; a.disabled = 1; a.exclude_kernel = 1; a.exclude_hv = 1;
  int fd = (int)syscall(SYS_perf_event_open, &a, 0, -1, -1, 0);
  if (fd < 0) {
    why = std::string("perf_event_open failed: ") + strerror(errno) + " (kernel.perf_event_paranoid=" +
          slurp("/proc/sys/kernel/perf_event_paranoid") +
          "; try: sudo sysctl kernel.perf_event_paranoid=2, or run as root; virtual machines usually expose no PMU)";
    return nullptr;
  }
  auto c = std::make_unique<PerfCounter>();
  c->fd = fd;
  c->label = "linux-perf_event_open(user mode, per-thread)";
  return c;
}
#elif defined(_WIN32) && SMC_X64
struct PawnIo {
  HMODULE dll = nullptr;
  HANDLE h = nullptr;
  HRESULT(STDAPICALLTYPE* open_)(PHANDLE) = nullptr;
  HRESULT(STDAPICALLTYPE* load_)(HANDLE, const UCHAR*, SIZE_T) = nullptr;
  HRESULT(STDAPICALLTYPE* exec_)(HANDLE, PCSTR, const ULONG64*, SIZE_T, PULONG64, SIZE_T, PSIZE_T) = nullptr;
  HRESULT(STDAPICALLTYPE* close_)(HANDLE) = nullptr;
  bool init(const std::string& lib, const std::string& blobPath, std::string& why) {
    dll = LoadLibraryA(lib.c_str());
    if (!dll) { why = "PawnIOLib.dll not found (install PawnIO, Official edition, from https://pawnio.eu)"; return false; }
    open_ = (decltype(open_))GetProcAddress(dll, "pawnio_open");
    load_ = (decltype(load_))GetProcAddress(dll, "pawnio_load");
    exec_ = (decltype(exec_))GetProcAddress(dll, "pawnio_execute");
    close_ = (decltype(close_))GetProcAddress(dll, "pawnio_close");
    if (!open_ || !load_ || !exec_) { why = "PawnIOLib.dll lacks the expected exports"; return false; }
    FILE* f = fopen(blobPath.c_str(), "rb");
    if (!f) { why = "module blob not found: " + blobPath; return false; }
    std::vector<unsigned char> b;
    unsigned char buf[4096];
    size_t n;
    while ((n = fread(buf, 1, sizeof buf, f)) > 0) b.insert(b.end(), buf, buf + n);
    fclose(f);
    HRESULT hr = open_(&h);
    if (FAILED(hr)) {
      char m[128];
      snprintf(m, sizeof m, "pawnio_open failed: 0x%08lX (driver not installed, or not running as administrator)", (unsigned long)hr);
      why = m;
      return false;
    }
    hr = load_(h, b.data(), b.size());
    if (FAILED(hr)) {
      char m[128];
      snprintf(m, sizeof m, "pawnio_load failed: 0x%08lX (module rejected)", (unsigned long)hr);
      why = m;
      return false;
    }
    return true;
  }
  ~PawnIo() { if (h && close_) close_(h); }
  bool rd(uint32_t msr, uint64_t& v) {
    ULONG64 in = msr, out = 0;
    SIZE_T n = 0;
    if (FAILED(exec_(h, "ioctl_read_msr", &in, 1, &out, 1, &n)) || n < 1) return false;
    v = out;
    return true;
  }
  bool wr(uint32_t msr, uint64_t v) {
    ULONG64 in[2] = {msr, v};
    SIZE_T n = 0;
    ULONG64 out = 0;
    return SUCCEEDED(exec_(h, "ioctl_write_msr", in, 2, &out, 0, &n));
  }
};

struct PawnCounter : Counter {
  PawnIo io;
  uint64_t cfg = 0;
  static constexpr uint32_t EVT = 0xC0010000, CTR = 0xC0010004;
  bool start() override {
    uint64_t sel = (cfg & 0xFFFFull) | (cfg & 0xF00000000ull) | (1ull << 16) | (1ull << 22);  // USR | EN, ring 0 excluded
    return io.wr(EVT, 0) && io.wr(CTR, 0) && io.wr(EVT, sel);
  }
  bool stop(uint64_t& v) override {
    io.wr(EVT, 0);
    uint64_t r;
    if (!io.rd(CTR, r)) return false;
    v = r & ((1ull << 48) - 1);
    return true;
  }
  std::string name() const override { return "windows-PawnIO AMDFamily17 (PerfEvtSel0/PerfCtr0, user mode, per-core)"; }
};

std::unique_ptr<Counter> openCounterWin(const Cpu& c, uint64_t cfg, const std::string& lib, const std::string& blob, std::string& why) {
  if (c.vendor != "AuthenticAMD") {
    why = "PawnIO's stock IntelMSR module permits only power/thermal MSRs; Intel PMU MSRs are denied, so no counter is available on Windows/Intel";
    return nullptr;
  }
  auto p = std::make_unique<PawnCounter>();
  p->cfg = cfg;
  if (!p->io.init(lib, blob, why)) return nullptr;
  SetThreadAffinityMask(GetCurrentThread(), (DWORD_PTR)1 << (GetCurrentProcessorNumber() & 63));  // per-core counter follows this thread
  SetThreadPriority(GetCurrentThread(), THREAD_PRIORITY_HIGHEST);
  return p;
}
#endif

// ---- the self-modifying kernel -------------------------------------------------------------------------------------
// 0:  B8 90 00 00 00     mov eax,0x90
// 5:  BA n32             mov edx,n
// 10: 88 05 rel32        L: mov [rip+rel32],al      (stores 0x90 at buffer offset T = 16 + rel32)
// 16: 90 x6              nops (T=16 is executed next: the store hits code about to run)
// 22: FF CA              dec edx
// 24: 75 F0              jnz L
// 26: C3                 ret
const size_t kLoop = 10, kEnd = 16;

struct Code {
  unsigned char* p = nullptr;
  size_t size = 3 * 4096;
  bool alloc(std::string& why) {
#ifdef _WIN32
    p = (unsigned char*)VirtualAlloc(nullptr, size, MEM_COMMIT | MEM_RESERVE, PAGE_EXECUTE_READWRITE);
#else
    void* m = mmap(nullptr, size, PROT_READ | PROT_WRITE | PROT_EXEC, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    p = m == MAP_FAILED ? nullptr : (unsigned char*)m;
#endif
    if (!p) why = "cannot allocate read-write-execute memory (hardened OS policy?)";
    return p != nullptr;
  }
  void set(uint32_t n, uint32_t target) {
    memset(p, 0, size);
    const unsigned char t[] = {0xB8, 0x90, 0, 0, 0, 0xBA, 0, 0, 0, 0, 0x88, 0x05, 0, 0, 0, 0,
                               0x90, 0x90, 0x90, 0x90, 0x90, 0x90, 0xFF, 0xCA, 0x75, 0xF0, 0xC3};
    memcpy(p, t, sizeof t);
    memcpy(p + 6, &n, 4);
    int32_t rel = (int32_t)target - (int32_t)kEnd;
    memcpy(p + kLoop + 2, &rel, 4);
  }
  void run() { ((void (*)())p)(); }
};

struct Case { const char* name; uint32_t target; };
const Case kCases[] = {
    {"store into the next executed instruction (+0)", 16},
    {"store 64 bytes ahead, same page", 80},
    {"store 1024 bytes ahead, same page", 1040},
    {"store at the start of the next page", 4096},
    {"store two pages ahead", 8192},
};

double median(std::vector<double> v) {
  std::sort(v.begin(), v.end());
  return v[v.size() / 2];
}

}  // namespace

int main(int argc, char** argv) {
  uint32_t iters = 100000;
  int reps = 7;
  long long evOverride = -1;
  bool selftest = false;
  std::string jsonPath, lib = "PawnIOLib.dll", blob = "AMDFamily17.bin";
  for (int i = 1; i < argc; i++) {
    std::string a = argv[i];
    auto next = [&]() { return i + 1 < argc ? std::string(argv[++i]) : std::string(); };
    if (a == "--iters") iters = (uint32_t)atoi(next().c_str());
    else if (a == "--reps") reps = atoi(next().c_str());
    else if (a == "--event") evOverride = (long long)strtoull(next().c_str(), nullptr, 0);
    else if (a == "--json") jsonPath = next();
    else if (a == "--pawnio-lib") lib = next();
    else if (a == "--pawnio-module") blob = next();
    else if (a == "--selftest") selftest = true;
    else {
      fprintf(stderr, "usage: smc_pmc_probe [--iters N] [--reps R] [--event RAWCFG] [--json FILE] [--pawnio-lib DLL] [--pawnio-module BIN] [--selftest]\n");
      return 2;
    }
  }
  if (iters == 0 || reps <= 0) return 2;
  Cpu cpu = cpuInfo();
  printf("cpu: vendor=%s family=%02Xh model=%02Xh stepping=%u hypervisor=%s\n", cpu.vendor.c_str(), cpu.family, cpu.model, cpu.stepping,
         cpu.hypervisor ? "yes" : "no");
  if (!SMC_X64) {
    printf("result: unsupported architecture (x86-64 only)\n");
    return selftest ? 0 : 3;
  }

  EventChoice ev = chooseEvent(cpu, evOverride);
  std::unique_ptr<Counter> ctr;
  std::string why = ev.why;
  if (ev.have && !selftest) {
#if defined(__linux__) && SMC_X64
    ctr = openCounter(ev.cfg, why);
#elif defined(_WIN32) && SMC_X64
    ctr = openCounterWin(cpu, ev.cfg, lib, blob, why);
#else
    why = "no counter backend on this operating system (timing only)";
#endif
  }
  if (ctr) printf("counter: %s, event %s (raw 0x%llX)\n", ctr->name().c_str(), ev.why.c_str(), (unsigned long long)ev.cfg);
  else printf("counter: none (%s); timing only\n", selftest ? "selftest" : why.c_str());

  Code code;
  std::string cw;
  if (!code.alloc(cw)) {
    printf("result: %s\n", cw.c_str());
    return selftest ? 0 : 4;
  }

  std::string json = "{\"vendor\":\"" + cpu.vendor + "\",\"family\":" + std::to_string(cpu.family) + ",\"model\":" + std::to_string(cpu.model) +
                     ",\"hypervisor\":" + (cpu.hypervisor ? "true" : "false") + ",\"counter\":" + (ctr ? "true" : "false") +
                     ",\"iters\":" + std::to_string(iters) + ",\"cases\":[";
  for (size_t ci = 0; ci < sizeof kCases / sizeof *kCases; ci++) {
    code.set(1000, kCases[ci].target);
    code.run();  // warm-up
    std::vector<double> ns, cnt;
    for (int r = 0; r < reps; r++) {
      code.set(iters, kCases[ci].target);
      uint64_t c0 = 0;
      bool cok = ctr && ctr->start();
      auto t0 = std::chrono::steady_clock::now();
      code.run();
      auto t1 = std::chrono::steady_clock::now();
      if (cok && !ctr->stop(c0)) cok = false;
      ns.push_back(std::chrono::duration<double, std::nano>(t1 - t0).count() / iters);
      if (cok) cnt.push_back((double)c0);
    }
    double mn = median(ns);
    std::string sep = ci ? "," : "";
    if (ctr && !cnt.empty()) {
      double mc = median(cnt);
      printf("%-48s %9.2f ns/iter  %12.0f clears (median of %d) = %.4f per iteration\n", kCases[ci].name, mn, mc, reps, mc / iters);
      json += sep + "{\"case\":\"" + kCases[ci].name + "\",\"ns_per_iter\":" + std::to_string(mn) + ",\"count\":" + std::to_string(mc) + "}";
    } else {
      printf("%-48s %9.2f ns/iter  (no counter)\n", kCases[ci].name, mn);
      json += sep + "{\"case\":\"" + kCases[ci].name + "\",\"ns_per_iter\":" + std::to_string(mn) + "}";
    }
  }
  json += "]}\n";
  if (!jsonPath.empty()) {
    FILE* f = fopen(jsonPath.c_str(), "wb");
    if (f) { fputs(json.c_str(), f); fclose(f); }
  }
  printf("result: %s\n", ctr ? "counter measurements above are evidence about this machine only" : "timing only; no counter was available");
  return 0;
}
