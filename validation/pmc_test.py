"""Build and run the portable SMC counter probe on this machine and save the output.

    python validation/pmc_test.py                 # Linux, macOS, Windows
    python validation/pmc_test.py --event 0x0461  # AMD Zen: raw event override (see validation/pmc/README.md)

Windows + AMD: the Official PawnIO driver (https://pawnio.eu) must be installed and this must run from an administrator
prompt; the pinned official module AMDFamily17.bin is fetched from the PawnIO.Modules release and hash-checked.
Linux: no driver; if perf_event_open is refused the probe says which sysctl to change.
The output is measurement evidence about this machine, never proof.
"""
import argparse
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


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--event", help="raw event config override, e.g. 0x04C3")
    ap.add_argument("--iters", type=int, default=100000)
    ap.add_argument("--reps", type=int, default=7)
    ap.add_argument("--pawnio-lib")
    a = ap.parse_args()

    exe = build()
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
    r = run(cmd)
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
