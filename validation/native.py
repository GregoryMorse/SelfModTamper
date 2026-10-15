"""Compile SelfModTamper.sln configurations (Debug|x64, Release|x64) with MSBuild.

The product needs administrator rights and the WinRing0 driver to *run* (it reads MSRs and issues an IOCTL),
so this script only compiles it (evidence that the sources build; no behaviour is claimed).  Later rounds add
the evidence harness validation/native/smc_harness.cpp (plan R12), which does run.
Usage: python validation/native.py [--toolset v143] [--configs "Debug|x64" ...]"""
import argparse, json, subprocess, sys, time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
VSWHERE = Path(r"C:\Program Files (x86)\Microsoft Visual Studio\Installer\vswhere.exe")


def vcvars() -> Path:
    out = subprocess.run([str(VSWHERE), "-latest", "-property", "installationPath"],
                         capture_output=True, text=True).stdout.strip()
    return Path(out) / r"VC\Auxiliary\Build\vcvarsall.bat"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--toolset")
    ap.add_argument("--configs", nargs="*", default=["Debug|x64", "Release|x64"])
    a = ap.parse_args()
    results = {}
    for cfg in a.configs:
        conf, plat = cfg.split("|")
        ts = f" /p:PlatformToolset={a.toolset}" if a.toolset else ""
        cmd = (f'call "{vcvars()}" x64 >nul && msbuild SelfModTamper.sln /nologo /v:m '
               f'/p:Configuration={conf} /p:Platform={plat}{ts}')
        start = time.time()
        b = subprocess.run('cmd /s /c "' + cmd + '"', cwd=ROOT, capture_output=True, text=True, errors="replace")
        rec = {"build_ok": b.returncode == 0, "build_seconds": round(time.time() - start)}
        if b.returncode:
            rec["build_tail"] = (b.stdout + b.stderr)[-2500:]
        results[cfg] = rec
        print(cfg, json.dumps(rec), flush=True)
    return 0 if all(v["build_ok"] for v in results.values()) else 1


if __name__ == "__main__":
    sys.exit(main())
