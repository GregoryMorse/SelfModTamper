"""Build and run the evidence harness validation/native/smc_harness.cpp (cl.exe + the vcpkg AsmJit of this repository),
then write validation/layout/dyn_x64.json from the dumped bytes of `gen_asm` (the AsmJit-generated dynamic kernel).
Usage (under the memory guard): python validation/limited_run.py -- python validation/native_harness.py
Evidence, not proof: the bytes are what this AsmJit version emitted on this machine."""
import json, re, shutil, subprocess, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
B = ROOT / "validation/.build/native"
B.mkdir(parents=True, exist_ok=True)
VSWHERE = Path(r"C:\Program Files (x86)\Microsoft Visual Studio\Installer\vswhere.exe")
VC = ROOT / "vcpkg_installed/x64-windows/x64-windows"
NL = chr(13) + chr(10)


def vcvars() -> Path:
    out = subprocess.run([str(VSWHERE), "-latest", "-property", "installationPath"],
                         capture_output=True, text=True).stdout.strip()
    return Path(out) / r"VC\Auxiliary\Build\vcvarsall.bat"


def runbat(name: str, lines: list) -> subprocess.CompletedProcess:
    f = B / name
    f.write_text(NL.join(["@echo off", f'call "{vcvars()}" x64 >nul'] + lines) + NL)
    return subprocess.run(["cmd", "/c", str(f)], cwd=B, capture_output=True, text=True, stdin=subprocess.DEVNULL)


def main() -> int:
    r = runbat("ml.bat", [f'ml64 /nologo /c /Fo TP.obj /Fl"TP.lst" /Sa "{ROOT / "SelfModTamper/TP.asm"}"'])
    print(r.stdout[-1500:], r.stderr[-800:])
    if r.returncode:
        return r.returncode
    cl = (f'cl /nologo /EHsc /permissive- /O1 /MD /DUNICODE /D_UNICODE /D_CONSOLE /DNDEBUG /I "{VC / "include"}" "{ROOT / "validation/native/smc_harness.cpp"}" '
          f'TP.obj /Fe:smc_harness.exe /link /LIBPATH:"{VC / "lib"}" asmjit.lib kernel32.lib user32.lib Mincore.lib Winmm.lib')
    r = runbat("cl.bat", [cl])
    print(r.stdout[-2500:], r.stderr[-800:])
    if r.returncode:
        return r.returncode
    shutil.copy(VC / "bin/asmjit.dll", B / "asmjit.dll")
    r = subprocess.run([str(B / "smc_harness.exe"), "--dump-dyn", "dyn.bin"], cwd=B, capture_output=True, text=True)
    print(r.stdout[-1500:], r.stderr[-500:], r.returncode)
    if r.returncode:
        return r.returncode
    data = (B / "dyn.bin").read_bytes()
    m = re.search(r"Intro bytes: 0x([0-9A-F]+) Code size: 0x([0-9A-F]+)", r.stdout)
    out = {"source": "gen_asm via validation/native/smc_harness.cpp", "size": len(data), "bytes": list(data),
           "printed": {"line": r.stdout.splitlines()[0] if r.stdout else "",
                       "intro_bytes": int(m.group(1), 16) if m else None,
                       "code_size": int(m.group(2), 16) if m else None}}
    (ROOT / "validation/layout").mkdir(exist_ok=True)
    (ROOT / "validation/layout/dyn_x64.json").write_text(json.dumps(out) + "\n")
    print("dyn_x64.json", len(data), out["printed"])
    return 0


sys.exit(main())
