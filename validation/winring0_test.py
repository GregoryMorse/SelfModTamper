"""WinRing0 run of the benchmark product, before and after the R12 fixes, with everything saved for analysis.

  python validation/winring0_test.py [--only post|pre] [--timeout SECONDS] [--rebuild]

Run it from any prompt; it re-launches itself elevated (UAC) when needed.  Everything goes to
validation/native/winring0/<timestamp>/ :
  sysinfo.json         OS, CPU, Memory integrity (HVCI), vulnerable-driver blocklist, driver file hash, driver service state, recent
                       Code Integrity events that mention WinRing0 (these show why a load was blocked)
  <variant>/stdout.txt the product's output (MACHINE_CLEARS.SMC per trial and the timing rows), also echoed to this console
  <variant>/out.txt    the RDTSCP samples the product writes;  <variant>/func.asm  the dynamically generated kernel listing
  summary.json         exit codes, durations, whether the event counter was non-zero, the per-kernel table
Send me the folder (or its summary.json and sysinfo.json).  The product is run from a copy in that folder, never from the repository
root, so nothing is left behind there.  The driver WinRing0x64.sys is built from source by scripts/Build-WinRing0.cmd (CMake, MSBuild, WDK; unsigned); if it is
blocked by Windows the product still runs and the event counters read 0 - sysinfo.json records why.

'pre' is the product built from the commit before the R12 fixes (git worktree ../SelfModTamper-prefix at 2e1b36c), 'post' is this tree.
Both are compiled by validation/build_product.py with the same flags; this is evidence about behaviour on this machine, not proof."""
import argparse, ctypes, datetime, hashlib, json, os, re, shutil, subprocess, sys, time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SRC = {"post": ROOT, "pre": ROOT.parent / "SelfModTamper-prefix"}
BUILD = ROOT / "validation/.build"
OUT = ROOT / "validation/native/winring0"
PRE_REF = "2e1b36c"


def is_admin() -> bool:
    try:
        return bool(ctypes.windll.shell32.IsUserAnAdmin())
    except Exception:
        return False


def elevate(argv):
    params = " ".join('"%s"' % a for a in [str(Path(__file__).resolve())] + argv + ["--elevated"])
    rc = ctypes.windll.shell32.ShellExecuteW(None, "runas", sys.executable, params, str(ROOT), 1)
    if rc <= 32:
        print("Elevation was refused or failed (code %d). Open an Administrator prompt and run this script again." % rc)
        return 1
    print("An elevated window was opened; the results are written to", OUT)
    return 0


def ps(cmd: str) -> str:
    r = subprocess.run(["powershell", "-NoProfile", "-Command", cmd], capture_output=True, text=True, errors="replace")
    return (r.stdout + r.stderr).strip()


def reg(path: str, name: str):
    out = ps(f"(Get-ItemProperty -Path '{path}' -Name '{name}' -ErrorAction SilentlyContinue).'{name}'")
    return out if out else None


def sysinfo(driver: Path) -> dict:
    info = {"time": datetime.datetime.now().isoformat(timespec="seconds"), "admin": is_admin()}
    info["os"] = ps("(Get-CimInstance Win32_OperatingSystem | ForEach-Object { $_.Caption + ' ' + $_.Version + ' build ' + $_.BuildNumber })")
    info["cpu"] = ps("(Get-CimInstance Win32_Processor | ForEach-Object { $_.Name + ' / ' + $_.NumberOfCores + ' cores / ' + $_.NumberOfLogicalProcessors + ' threads' })")
    info["hypervisor_present"] = ps("(Get-CimInstance Win32_ComputerSystem).HypervisorPresent")
    info["memory_integrity_hvci_enabled"] = reg(r"HKLM:\SYSTEM\CurrentControlSet\Control\DeviceGuard\Scenarios\HypervisorEnforcedCodeIntegrity", "Enabled")
    info["vulnerable_driver_blocklist_enabled"] = reg(r"HKLM:\SYSTEM\CurrentControlSet\Control\CI\Config", "VulnerableDriverBlocklistEnable")
    info["secure_boot"] = ps("try { Confirm-SecureBootUEFI } catch { 'unknown: ' + $_.Exception.Message }")
    info["device_guard"] = ps("(Get-CimInstance -ClassName Win32_DeviceGuard -Namespace root\\Microsoft\\Windows\\DeviceGuard -ErrorAction SilentlyContinue | "
                              "Select-Object SecurityServicesRunning,SecurityServicesConfigured | ConvertTo-Json -Compress)")
    info["driver_file"] = str(driver) if driver.exists() else None
    if driver.exists():
        info["driver_sha256"] = hashlib.sha256(driver.read_bytes()).hexdigest()
        info["driver_size"] = driver.stat().st_size
        info["driver_signature"] = ps(f"(Get-AuthenticodeSignature -FilePath '{driver}' | ForEach-Object {{ $_.Status.ToString() + ' / ' + $_.SignerCertificate.Subject }})")
    info["driver_service"] = ps("sc.exe query WinRing0_1_2_0")
    info["code_integrity_events_winring0"] = ps(
        "Get-WinEvent -LogName 'Microsoft-Windows-CodeIntegrity/Operational' -MaxEvents 300 -ErrorAction SilentlyContinue | "
        "Where-Object { $_.Message -match 'WinRing0' } | Select-Object -First 10 | ForEach-Object { $_.TimeCreated.ToString('s') + ' id=' + $_.Id + ' ' + ($_.Message -replace '\\s+',' ') }")
    return info


SVC = "WinRing0_1_2_0"
# The signed 1.2.0 driver as committed to the xmrig repository (2019-12-14), pinned by commit and by git blob id (verified before anything is
# written to disk).  WinRing0 1.2.0 is a KNOWN VULNERABLE driver (CVE-2020-14979, CVE-2021-41285: arbitrary MSR / physical-memory access
# for any caller) and is on Microsoft's vulnerable-driver blocklist, so this script loads it only for the run and removes the service at
# once, also when the run fails.
SIGNED_URL = "https://raw.githubusercontent.com/xmrig/xmrig/a6f381403cc8ffda6836bdd31ddd6e7677c2b6d1/bin/WinRing0/WinRing0x64.sys"
SIGNED_BLOB = "197c255adea745c8a78f529c8a38a3ceaf68711d"
SIGNED_DIR = BUILD / "winring0-signed"


def remove_service() -> str:
    """Stop and delete the driver service; return a one-line state ('absent' when it is gone)."""
    ps_out = ps(f"sc.exe query {SVC}")
    if "1060" in ps_out:
        return "absent"
    ps(f"sc.exe stop {SVC}")
    for _ in range(20):
        if "STOPPED" in ps(f"sc.exe query {SVC}") or "1060" in ps(f"sc.exe query {SVC}"):
            break
        time.sleep(0.5)
    ps(f"sc.exe delete {SVC}")
    for _ in range(20):
        if "1060" in ps(f"sc.exe query {SVC}"):
            return "absent"
        time.sleep(0.5)
    return "STILL REGISTERED (a reboot removes a service marked for deletion)"


def download_signed() -> Path:
    import urllib.request
    dst = SIGNED_DIR / "WinRing0x64.sys"
    if dst.exists():
        return dst
    print("Downloading the signed WinRing0x64.sys (pinned xmrig commit) ...")
    data = urllib.request.urlopen(SIGNED_URL, timeout=120).read()
    blob = hashlib.sha1(b"blob %d\x00" % len(data) + data).hexdigest()
    if blob != SIGNED_BLOB:
        raise SystemExit(f"downloaded file has git blob id {blob}, expected {SIGNED_BLOB}: refusing to use it")
    SIGNED_DIR.mkdir(parents=True, exist_ok=True)
    dst.write_bytes(data)
    time.sleep(2)
    if not dst.exists() or dst.stat().st_size != len(data):
        raise SystemExit(
            "Windows Defender removed the driver (it is a known vulnerable driver).  Re-run with --defender-exclusion, which excludes only "
            f"{SIGNED_DIR} for the duration of the run and removes the exclusion afterwards.")
    return dst


def find_built() -> Path:
    for p in [ROOT / "WinRing0x64.sys", BUILD / "WinRing0x64.sys", ROOT / "x64/Release/WinRing0x64.sys"]:
        if p.exists():
            return p
    return ROOT / "WinRing0x64.sys"


def ensure_driver(kind: str, testsign: bool = False) -> Path:
    if kind == "signed":
        return download_signed()
    d = find_built()
    if not d.exists():
        script = ROOT / "scripts/Build-WinRing0.cmd"
        print("WinRing0x64.sys not found; building it from source with", script)
        subprocess.run(["cmd", "/c", str(script)] + (["-DWINRING0_TESTSIGN=ON"] if testsign else []), cwd=ROOT)
        d = find_built()
    return d


def ensure_build(variant: str, rebuild: bool) -> Path:
    exe = BUILD / f"product_{variant}" / "SelfModTamper.exe"
    if exe.exists() and not rebuild:
        return exe
    src = SRC[variant]
    if variant == "pre" and not src.exists():
        subprocess.run(["git", "worktree", "add", str(src), PRE_REF], cwd=ROOT)
    r = subprocess.run([sys.executable, str(ROOT / "validation/build_product.py"), str(src), str(BUILD / f"product_{variant}")], cwd=ROOT)
    if r.returncode or not exe.exists():
        raise SystemExit(f"could not build the {variant} product (needs Visual Studio with the C++ workload and vcpkg_installed)")
    return exe


def run_variant(variant: str, exe: Path, driver: Path, dest: Path, timeout: int) -> dict:
    wd = dest / variant
    wd.mkdir(parents=True, exist_ok=True)
    shutil.copy(exe, wd / "SelfModTamper.exe")
    shutil.copy(exe.parent / "asmjit.dll", wd / "asmjit.dll")
    if driver.exists():
        shutil.copy(driver, wd / "WinRing0x64.sys")
    print(f"\n=== {variant}: {exe} ===", flush=True)
    start = time.time()
    rec = {"variant": variant, "exe_sha256": hashlib.sha256(exe.read_bytes()).hexdigest()}
    with open(wd / "stdout.txt", "w", encoding="utf-8", errors="replace") as f:
        p = subprocess.Popen([str(wd / "SelfModTamper.exe")], cwd=wd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                             stdin=subprocess.DEVNULL, text=True, errors="replace")
        n = 0
        try:
            for line in p.stdout:
                f.write(line)
                n += 1
                if not line.startswith("MACHINE_CLEARS") or n % 5000 == 0:
                    print(line.rstrip(), flush=True)
                if time.time() - start > timeout:
                    p.kill()
                    rec["timed_out"] = True
                    break
        finally:
            p.wait()
    rec.update(exit_code=p.returncode, seconds=round(time.time() - start, 1), lines=n)
    rec["kernels"] = parse(wd / "stdout.txt")
    for extra in ("out.txt", "func.asm"):
        rec[extra] = (wd / extra).exists()
    return rec


def parse(path: Path) -> list:
    """Per kernel: name, the per-trial MACHINE_CLEARS counts summarised, the final total, and the timing rows (avg min max per timer)."""
    names = {"C", "SMC", "C Loop", "Dyn SMC Loop", "SMC Loop"}
    res, cur, vals = [], None, []
    def close():
        if cur is not None:
            total = vals[-1] if vals else None
            per = vals[:-1]
            cur.update(total=total, trials=len(per), nonzero_trials=sum(1 for v in per if v), per_trial_min=min(per, default=None),
                       per_trial_max=max(per, default=None), per_trial_mean=(sum(per) / len(per) if per else None))
    for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
        s = line.strip()
        if s in names:
            close()
            cur, vals = {"kernel": s, "timing_rows": []}, []
            res.append(cur)
        elif cur is not None and s.startswith("MACHINE_CLEARS.SMC:"):
            vals.append(int(s.split(":")[1]))
        elif cur is not None and re.fullmatch(r"\d+ \d+ \d+", s):
            cur["timing_rows"].append([int(x) for x in s.split()])
    close()
    return res


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--only", choices=["pre", "post"])
    ap.add_argument("--timeout", type=int, default=3600, help="seconds per variant")
    ap.add_argument("--rebuild", action="store_true", help="recompile both products even if validation/.build has them")
    ap.add_argument("--driver", choices=["signed", "build"], default="signed",
                    help="signed: the Microsoft-signed 1.2.0 driver from a pinned xmrig commit (default, loads without test-signing); build: built from source (unsigned)")
    ap.add_argument("--defender-exclusion", action="store_true", help="exclude the driver download directory from Defender for the run only")
    ap.add_argument("--testsign", action="store_true", help="test-sign the driver when it is built (loads only in Windows test-signing mode)")
    ap.add_argument("--elevated", action="store_true", help=argparse.SUPPRESS)
    a = ap.parse_args()
    if not is_admin():
        return elevate([x for x in sys.argv[1:] if x != "--elevated"])
    excl = False
    try:
        if a.defender_exclusion:
            ps(f"Add-MpPreference -ExclusionPath '{SIGNED_DIR}'")
            excl = True
        dest = OUT / datetime.datetime.now().strftime("%Y%m%d-%H%M%S")
        dest.mkdir(parents=True, exist_ok=True)
        print("Removing any leftover driver service first:", remove_service())
        driver = ensure_driver(a.driver, a.testsign)
        info = sysinfo(driver)
        info["driver_kind"] = a.driver
        (dest / "sysinfo.json").write_text(json.dumps(info, indent=2), encoding="utf-8")
        print(json.dumps(info, indent=2))
        variants = [a.only] if a.only else ["post", "pre"]
        exes = {v: ensure_build(v, rebuild=a.rebuild) for v in variants}
        summary = {"sysinfo": "sysinfo.json", "runs": []}
        for v in variants:
            try:
                summary["runs"].append(run_variant(v, exes[v], driver, dest, a.timeout))
            finally:
                # the vulnerable driver must not stay registered or on disk next to the run
                summary.setdefault("service_after", {})[v] = remove_service()
                (dest / v / "WinRing0x64.sys").unlink(missing_ok=True)
            (dest / "summary.json").write_text(json.dumps(summary, indent=2), encoding="utf-8")
        info["driver_service_after"] = remove_service()
        (dest / "sysinfo.json").write_text(json.dumps(info, indent=2), encoding="utf-8")
        print("\nDriver service after the run:", info["driver_service_after"])
        print("Done. Send me:", dest)
        return 0
    finally:
        print("Final cleanup, driver service:", remove_service())
        if excl:
            ps(f"Remove-MpPreference -ExclusionPath '{SIGNED_DIR}'")
        if a.elevated:
            input("\nPress Enter to close this window...")


if __name__ == "__main__":
    sys.exit(main())
