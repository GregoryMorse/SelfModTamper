"""Compile SelfModTamper.sln (Debug|x64, Release|x64) with MSBuild; output goes only to build/msbuild/<toolset>/.

The product needs administrator rights to read the counter on some platforms, so this script only compiles it (evidence that the
sources build; no behaviour is claimed).  asmjit is fetched by the project itself (cmake/fetch_asmjit.cmake, pinned and hash-checked).
Usage: python validation/native.py [--toolset v143|v145] [--configs "Debug|x64" ...]
The Visual Studio install is chosen from the toolset: v143 -> Visual Studio 2022, v145 -> Visual Studio 2026 (any install that has it);
without --toolset the latest install and its default toolset are used."""
import argparse, json, subprocess, sys, time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
VSWHERE = Path(r"C:\Program Files (x86)\Microsoft Visual Studio\Installer\vswhere.exe")
MAJOR = {"v143": "[17.0,18.0)", "v145": "[18.0,19.0)"}


def vcvars(toolset) -> Path:
    cmd = [str(VSWHERE), "-property", "installationPath"]
    cmd += ["-version", MAJOR[toolset]] if toolset in MAJOR else ["-latest"]
    out = subprocess.run(cmd, capture_output=True, text=True).stdout.strip().splitlines()
    if not out:
        sys.exit("no Visual Studio install for toolset %s" % toolset)
    return Path(out[0]) / r"VC\Auxiliary\Build\vcvarsall.bat"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--toolset")
    ap.add_argument("--configs", nargs="*", default=["Debug|x64", "Release|x64"])
    a = ap.parse_args()
    results = {}
    for cfg in a.configs:
        conf, plat = cfg.split("|")
        ts = f" /p:PlatformToolset={a.toolset}" if a.toolset else ""
        cmd = (f'call "{vcvars(a.toolset)}" x64 >nul && msbuild SelfModTamper.sln /nologo /v:m '
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
