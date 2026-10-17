"""Build and run the portable SMC counter probe on this machine and save the output.

    python validation/pmc_test.py                 # Linux, macOS, Windows
    python validation/pmc_test.py --event 0x0461  # AMD Zen: raw event override (see validation/pmc/README.md)

Windows + AMD: the Official PawnIO driver (https://pawnio.eu) must be installed and this must run from an administrator
prompt; the pinned official module AMDFamily17.bin is fetched from the PawnIO.Modules release and hash-checked.
Linux: no driver; if perf_event_open is refused the probe says which sysctl to change.
The output is measurement evidence about this machine, never proof.
"""
import argparse
import ctypes
import re
import hashlib
import io
import json
import os
import platform
import shutil
import subprocess
import sys
import time
import urllib.request
import zipfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "validation" / "pmc"
BUILD = ROOT / "validation" / ".build" / "pmc"
OUT = ROOT / "validation" / "native" / "pmc"

MODULES_URL = "https://github.com/namazso/PawnIO.Modules/releases/download/0.2.11/release_0_2_11.zip"
MODULES_SHA256 = "43608cb89bc84247fef1368a139013f7d043e17db6d6c8dfc9b46bf0905a81f4"
AMD_MODULE_SHA256 = "dae74615761b78bdf064dfb3e136252ddcc6fc727d88f14738d0e5800d427a91"


def run(cmd, **kw):
    return subprocess.run(cmd, text=True, capture_output=True, **kw)


def build():
    r = run(["cmake", "-S", str(SRC), "-B", str(BUILD), "-DCMAKE_BUILD_TYPE=Release"])
    if r.returncode:
        sys.exit("cmake configure failed:\n" + r.stdout + r.stderr)
    r = run(["cmake", "--build", str(BUILD), "--config", "Release"])
    if r.returncode:
        sys.exit("cmake build failed:\n" + r.stdout + r.stderr)
    for name in ("smc_pmc_probe", "smc_pmc_probe.exe"):
        for p in BUILD.rglob(name):
            if p.is_file():
                return p
    sys.exit("probe executable not found after build")


def fetch_amd_module():
    dest = BUILD / "AMDFamily17.bin"
    if dest.exists() and hashlib.sha256(dest.read_bytes()).hexdigest() == AMD_MODULE_SHA256:
        return dest
    data = urllib.request.urlopen(MODULES_URL, timeout=60).read()
    if hashlib.sha256(data).hexdigest() != MODULES_SHA256:
        sys.exit("PawnIO.Modules release hash mismatch; refusing to use it")
    blob = zipfile.ZipFile(io.BytesIO(data)).read("AMDFamily17.bin")
    if hashlib.sha256(blob).hexdigest() != AMD_MODULE_SHA256:
        sys.exit("AMDFamily17.bin hash mismatch; refusing to use it")
    dest.write_bytes(blob)
    return dest


def pawnio_lib():
    for base in (os.environ.get("ProgramFiles", r"C:\Program Files"), os.environ.get("ProgramW6432", r"C:\Program Files")):
        p = Path(base) / "PawnIO" / "PawnIOLib.dll"
        if p.exists():
            return str(p)
    return "PawnIOLib.dll"


WPRP = """<?xml version="1.0" encoding="utf-8"?>
<WindowsPerformanceRecorder Version="1.0">
<Profiles>
    <SystemCollector Id="SystemCollector_SMC" Name="WPRSystemCollector">
      <BufferSize Value="1024" />
      <Buffers Value="64" />
    </SystemCollector>
    <SystemProvider Id="SystemProvider_SMC">
      <Keywords>
        <Keyword Value="Loader"/>
        <Keyword Value="ProcessThread"/>
        <Keyword Value="PmcProfile" />
      </Keywords>
    </SystemProvider>
    <MicroArchitecturalConfig Id="CounterConfig_SMC">
      <ProfileSources Architecture="{arch}" Family="{family}" Model="{model}" Stepping="{stepping}">
         <ProfileSource Name="MACHINE_CLEARS.SMC" Event="{event}" Unit="{unit}" Interval="0x00010000" AllowsHalt="false" Persist="true"/>
      </ProfileSources>
    </MicroArchitecturalConfig>
    <HardwareCounter Id="HardwareCounters_SMC">
        <MicroArchitecturalConfigId Value="CounterConfig_SMC"></MicroArchitecturalConfigId>
        <SampledCounters>
          <SampledCounter Value="MACHINE_CLEARS.SMC" Interval="2147483647"/>
        </SampledCounters>
    </HardwareCounter>
    <Profile Id="SMC.Verbose.File" LoggingMode="File" Name="SMC" DetailLevel="Verbose" Description="SMC machine clears">
        <Collectors Operation="Add">
            <SystemCollectorId Value="SystemCollector_SMC">
                <SystemProviderId Value="SystemProvider_SMC"></SystemProviderId>
                <HardwareCounterId Value="HardwareCounters_SMC"></HardwareCounterId>
            </SystemCollectorId>
        </Collectors>
    </Profile>
</Profiles>
</WindowsPerformanceRecorder>
"""


def register_wpr(exe, event):
    """Windows, administrator prompt: register MACHINE_CLEARS.SMC as a persistent hardware-counter profile source."""
    if not ctypes.windll.shell32.IsUserAnAdmin():
        sys.exit("--register-wpr needs an administrator prompt")
    r = run([str(exe), "--selftest", "--iters", "1000", "--reps", "1"])
    m = re.search(r"vendor=(\w+) family=([0-9A-F]+)h model=([0-9A-F]+)h stepping=(\d+)", r.stdout)
    if not m:
        sys.exit("cannot read the CPU identity from the probe:\n" + r.stdout + r.stderr)
    vendor, fam, mod, step = m.group(1), int(m.group(2), 16), int(m.group(3), 16), int(m.group(4))
    arch = "INTEL" if vendor == "GenuineIntel" else "AMD"
    cfg = int(event, 0) if event else (0x04C3 if arch == "INTEL" else None)
    if cfg is None:
        sys.exit("AMD: no verified SMC event is built in; pass --event (see validation/pmc/README.md)")
    xml = WPRP.format(arch=arch, family=fam, model=mod, stepping=step, event="0x%X" % ((cfg & 0xFF) | ((cfg >> 32 & 0xF) << 8)), unit="0x%X" % (cfg >> 8 & 0xFF))
    path = BUILD / "smc.wprp"
    path.write_text(xml, encoding="utf-8")
    print("registering", arch, fam, mod, step, "event/unit", cfg)
    for cmd in ([ "wpr", "-start", str(path), "-filemode"], ["wpr", "-cancel"]):
        r = run(cmd)
        print(" ".join(cmd), "->", r.returncode, (r.stdout + r.stderr).strip()[:400])
    r = run([str(exe), "--list-sources"])
    print(r.stdout)
    ok = "MACHINE_CLEARS.SMC" in r.stdout
    print("registered: YES" if ok else "registered: NO - send this output to the author")
    return 0 if ok else 1


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--event", help="raw event config override, e.g. 0x04C3")
    ap.add_argument("--iters", type=int, default=100000)
    ap.add_argument("--reps", type=int, default=7)
    ap.add_argument("--pawnio-lib")
    ap.add_argument("--with-wpr", action="store_true", help="Windows, admin: keep a WPR session with the registered source running while the probe runs")
    ap.add_argument("--register-wpr", action="store_true", help="Windows, admin: register MACHINE_CLEARS.SMC as a Windows hardware-counter profile source")
    a = ap.parse_args()

    exe = build()
    if a.register_wpr:
        return register_wpr(exe, a.event)
    stamp = time.strftime("%Y%m%d-%H%M%S")
    outdir = OUT / stamp
    outdir.mkdir(parents=True, exist_ok=True)
    cmd = [str(exe), "--iters", str(a.iters), "--reps", str(a.reps), "--json", str(outdir / "probe.json")]
    if a.event:
        cmd += ["--event", a.event]
    if platform.system() == "Windows":
        cmd += ["--pawnio-lib", a.pawnio_lib or pawnio_lib()]
        try:
            cmd += ["--pawnio-module", str(fetch_amd_module())]
        except Exception as e:  # network or hash problem: the probe falls back to timing only
            print("PawnIO module not available:", e)
    wpr = BUILD / "smc.wprp"
    if a.with_wpr and wpr.exists():
        w = run(["wpr", "-start", str(wpr), "-filemode"])
        print("wpr -start ->", w.returncode, (w.stdout + w.stderr).strip()[:300])
    try:
        r = run(cmd)
    finally:
        if a.with_wpr and wpr.exists():
            run(["wpr", "-cancel"])
    (outdir / "probe.txt").write_text(r.stdout + r.stderr, encoding="utf-8")
    meta = {"time": stamp, "platform": platform.platform(), "machine": platform.machine(), "python": sys.version.split()[0],
            "command": cmd, "exit": r.returncode}
    (outdir / "meta.json").write_text(json.dumps(meta, indent=2), encoding="utf-8")
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    print(r.stdout + r.stderr)
    print("saved to", outdir)
    return 0


if __name__ == "__main__":
    sys.exit(main())
