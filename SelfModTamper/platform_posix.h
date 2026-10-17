// POSIX (Linux and macOS, x86-64) shim for SelfModTamper.cpp: the small part of the Windows API the benchmark uses, plus the hardware
// counter (perf_event_open, user mode, per thread) in place of the WinRing0 driver.  No driver is involved.
// The Windows build does not include this file.
#pragma once
#include <algorithm>
#include <cerrno>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <ctime>
#include <string>
#include <vector>

#include <cpuid.h>
#include <fcntl.h>
#include <pthread.h>
#include <sys/ioctl.h>
#include <sys/mman.h>
#include <unistd.h>
#ifdef __APPLE__
#include <mach-o/getsect.h>
#include <mach-o/ldsyms.h>
#else
#include <elf.h>
#include <link.h>
#include <linux/perf_event.h>
#include <sched.h>
#include <sys/syscall.h>
#endif
#include <x86intrin.h>

using std::max;
using std::min;

#define __cdecl __attribute__((ms_abi))  // TP.asm follows the Windows x64 convention (RCX, RDX, R8)
#define __int64 long long
#define NULL_HANDLE nullptr
#define MAXCHAR 0x7f
static inline int fopen_s(FILE** f, const char* name, const char* mode) { *f = fopen(name, mode); return *f ? 0 : errno; }

typedef uint8_t BYTE, *PBYTE, *LPBYTE;
typedef uint32_t DWORD;
typedef uint64_t DWORD64, ULONG64, ULONGLONG, *PULONG64;
typedef int32_t LONG32, *PLONG32;
typedef void* LPVOID;
typedef void* HANDLE;

union LARGE_INTEGER { struct { uint32_t LowPart; int32_t HighPart; }; int64_t QuadPart; };
union ULARGE_INTEGER { struct { uint32_t LowPart; uint32_t HighPart; }; uint64_t QuadPart; };
struct FILETIME { uint32_t dwLowDateTime, dwHighDateTime; };
struct SYSTEM_INFO { DWORD dwPageSize; };

static inline uint64_t smc_ns(clockid_t c) {
  timespec t;
  clock_gettime(c, &t);
  return (uint64_t)t.tv_sec * 1000000000ull + (uint64_t)t.tv_nsec;
}
// Same units as the Windows calls: interrupt time and FILETIME in 100 ns, performance counter in ns here, tick count in ms.
static inline void QueryInterruptTimePrecise(ULONGLONG* t) { *t = smc_ns(CLOCK_MONOTONIC) / 100; }
static inline void QueryPerformanceFrequency(LARGE_INTEGER* f) { f->QuadPart = 1000000000ll; }
static inline void QueryPerformanceCounter(LARGE_INTEGER* c) { c->QuadPart = (int64_t)smc_ns(CLOCK_MONOTONIC); }
static inline void GetSystemTimePreciseAsFileTime(FILETIME* ft) {
  uint64_t v = smc_ns(CLOCK_REALTIME) / 100;
  ft->dwLowDateTime = (uint32_t)v;
  ft->dwHighDateTime = (uint32_t)(v >> 32);
}
static inline ULONGLONG GetTickCount64() { return smc_ns(CLOCK_MONOTONIC) / 1000000; }
static inline DWORD timeGetTime() { return (DWORD)GetTickCount64(); }
static inline void timeBeginPeriod(int) {}
static inline void timeEndPeriod(int) {}

static inline void GetSystemInfo(SYSTEM_INFO* si) { si->dwPageSize = (DWORD)sysconf(_SC_PAGESIZE); }
static inline void smc_pin_thread() {
#ifndef __APPLE__
  cpu_set_t set;
  CPU_ZERO(&set);
  CPU_SET(0, &set);  // the Windows build pins to logical processor 0 as well
  pthread_setaffinity_np(pthread_self(), sizeof set, &set);
#endif  // macOS has no thread affinity to a given processor
}

#define MEM_RESERVE 1
#define MEM_COMMIT 2
#define MEM_RELEASE 4
#define PAGE_EXECUTE_READWRITE 0
static inline void* VirtualAlloc(void*, size_t n, int, int) {
  void* p = mmap(nullptr, n, PROT_READ | PROT_WRITE | PROT_EXEC, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  return p == MAP_FAILED ? nullptr : p;
}
template <class T> static inline bool VirtualLock(T p, size_t n) { return mlock((void*)p, n) == 0; }
template <class T> static inline bool VirtualUnlock(T p, size_t n) { return munlock((void*)p, n) == 0; }
template <class T> static inline bool VirtualFree(T p, size_t, int) { return true; }  // the Windows call releases the whole region; here the dynamic copy is simply left to process exit

// The code segment: the executable PT_LOAD segment of this program, made writable (the kernels modify themselves and the
// benchmark checksums the whole segment).  The size is rounded down to a multiple of 8 and moved off a multiple of 148 qwords
// (the kernels' preconditions, which main() checks).
#ifdef __APPLE__
// macOS: the __TEXT,__text section of this executable; the linker is told to give __TEXT rwx protection (cmake/posix.cmake).
static inline void GetCodeSegmentBaseSize(PBYTE& base, DWORD& size) {
  unsigned long n = 0;
  base = (PBYTE)getsectiondata(&_mh_execute_header, "__TEXT", "__text", &n);
  size_t m = n & ~(size_t)7;
  if (m && (m / 8) % 148 == 0) m -= 8;
  size = (DWORD)m;
}
__attribute__((constructor)) static void smc_text_writable() {
  unsigned long n = 0;
  uintptr_t t = (uintptr_t)getsectiondata(&_mh_execute_header, "__TEXT", "__text", &n);
  long pg = sysconf(_SC_PAGESIZE);
  uintptr_t b0 = t & ~(uintptr_t)(pg - 1);
  size_t len = ((t + n + pg - 1) & ~(uintptr_t)(pg - 1)) - b0;
  if (mprotect((void*)b0, len, PROT_READ | PROT_WRITE | PROT_EXEC) != 0)
    fprintf(stderr, "mprotect of the code segment failed: %s (the self-modifying kernels will fault)\n", strerror(errno));
}
// No hardware counter on macOS: the machine-clear columns read 0 (timing only).
static inline HANDLE enablePerfCounters(const std::wstring&, const std::wstring&) {
  printf("No performance counter on macOS; machine-clear counts will read 0\n");
  return nullptr;
}
static inline void disablePerfCounters(const std::wstring&, HANDLE) {}
static inline bool zeroSMCCount(HANDLE) { return false; }
static inline unsigned long long getSMCCount(HANDLE) { return 0; }
#else
static int smc_phdr_cb(struct dl_phdr_info* info, size_t, void* data) {
  if (info->dlpi_name && info->dlpi_name[0]) return 0;  // the main program is the first entry, with an empty name
  auto* out = (std::pair<PBYTE, size_t>*)data;
  for (int i = 0; i < info->dlpi_phnum; i++) {
    const Elf64_Phdr& ph = info->dlpi_phdr[i];
    if (ph.p_type == PT_LOAD && (ph.p_flags & PF_X)) {
      out[0].first = (PBYTE)(info->dlpi_addr + ph.p_vaddr);
      out[0].second = ph.p_memsz;
      return 1;
    }
  }
  return 1;
}
static inline void GetCodeSegmentBaseSize(PBYTE& base, DWORD& size) {
  std::pair<PBYTE, size_t> seg(nullptr, 0);
  dl_iterate_phdr(smc_phdr_cb, &seg);
  base = seg.first;
  size_t n = seg.second & ~(size_t)7;
  if (n && (n / 8) % 148 == 0) n -= 8;
  size = (DWORD)n;
}
// Windows links with /SECTION:.text,RWE; here the executable segment is made writable before main() (the kernels modify themselves).
__attribute__((constructor)) static void smc_text_writable() {
  std::pair<PBYTE, size_t> seg(nullptr, 0);
  dl_iterate_phdr(smc_phdr_cb, &seg);
  long pg = sysconf(_SC_PAGESIZE);
  uintptr_t b0 = (uintptr_t)seg.first & ~(uintptr_t)(pg - 1);
  size_t len = (((uintptr_t)seg.first + seg.second + pg - 1) & ~(uintptr_t)(pg - 1)) - b0;
  if (mprotect((void*)b0, len, PROT_READ | PROT_WRITE | PROT_EXEC) != 0)
    fprintf(stderr, "mprotect of the code segment failed: %s (the self-modifying kernels will fault)\n", strerror(errno));
}

// ---- hardware counter: perf_event_open, user mode, this thread; one counter that runs continuously -------------------------------
static int smc_perf_fd = -1;
static inline std::string smc_slurp(const char* p) {
  FILE* f = fopen(p, "r");
  char b[256] = {};
  if (f) { if (!fgets(b, sizeof b, f)) b[0] = 0; fclose(f); }
  std::string s = b;
  while (!s.empty() && (s.back() == '\n' || s.back() == '\r')) s.pop_back();
  return s;
}
// Raw event: Intel MACHINE_CLEARS.SMC (C3H/04H); AMD Family 10h/15h PMCx021; AMD Zen: ic_cache_inval.fill_invalidated (8Ch/01h),
// an instruction-cache-invalidation proxy.  Override with the environment variable SMC_EVENT (for example 0x04C3).
static inline HANDLE enablePerfCounters(const std::wstring&, const std::wstring&) {
  unsigned a = 0, b = 0, c = 0, d = 0;
  __get_cpuid(0, &a, &b, &c, &d);
  char v[13];
  memcpy(v, &b, 4); memcpy(v + 4, &d, 4); memcpy(v + 8, &c, 4); v[12] = 0;
  __get_cpuid(1, &a, &b, &c, &d);
  unsigned fam = (a >> 8) & 0xF;
  if (fam == 0xF) fam += (a >> 20) & 0xFF;
  uint64_t cfg = 0;
  const char* what = "";
  if (!strcmp(v, "GenuineIntel")) { cfg = 0x04C3; what = "Intel MACHINE_CLEARS.SMC"; }
  else if (!strcmp(v, "AuthenticAMD")) {
    if (fam == 0x10 || fam == 0x15) { cfg = 0x0021; what = "AMD PMCx021 pipeline restart due to SMC"; }
    else { cfg = 0x018C; what = "AMD ic_cache_inval.fill_invalidated (instruction-cache invalidation proxy)"; }
  }
  if (const char* e = getenv("SMC_EVENT")) { cfg = strtoull(e, nullptr, 0); what = "SMC_EVENT override"; }
  if (!cfg) { printf("No SMC event known for vendor %s; machine-clear counts will read 0\n", v); return nullptr; }
  uint32_t type = PERF_TYPE_RAW;
  std::string t = smc_slurp("/sys/bus/event_source/devices/cpu_core/type");  // hybrid Intel: raw events live on cpu_core
  if (!t.empty()) type = (uint32_t)atoi(t.c_str());
  perf_event_attr pa;
  memset(&pa, 0, sizeof pa);
  pa.type = type; pa.size = sizeof pa; pa.config = cfg; pa.exclude_kernel = 1; pa.exclude_hv = 1;
  smc_perf_fd = (int)syscall(SYS_perf_event_open, &pa, 0, -1, -1, 0);
  if (smc_perf_fd < 0) {
    printf("perf_event_open failed: %s (kernel.perf_event_paranoid=%s); machine-clear counts will read 0\n", strerror(errno),
           smc_slurp("/proc/sys/kernel/perf_event_paranoid").c_str());
    return nullptr;
  }
  printf("Counter: %s, raw event 0x%llX, perf_event_open (user mode, this thread)\n", what, (unsigned long long)cfg);
  return (HANDLE)(intptr_t)(smc_perf_fd + 1);
}
static inline void disablePerfCounters(const std::wstring&, HANDLE) {
  if (smc_perf_fd >= 0) close(smc_perf_fd);
  smc_perf_fd = -1;
}
static inline bool zeroSMCCount(HANDLE) { return smc_perf_fd >= 0 && ioctl(smc_perf_fd, PERF_EVENT_IOC_RESET, 0) == 0; }
static inline unsigned long long getSMCCount(HANDLE) {
  uint64_t v = 0;
  if (smc_perf_fd < 0 || read(smc_perf_fd, &v, sizeof v) != (ssize_t)sizeof v) return 0;
  return v;
}
#endif  // __APPLE__
