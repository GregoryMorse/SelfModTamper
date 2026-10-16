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


def build(cfg: str) -> int:
    """cfg 'release': /O1 and no incremental link (symbols are the code itself); 'debug': /Od and incremental link (symbols are
    `E9 rel32` thunks).  Both link /SECTION:.text,RWE as the product does (the static SMC kernels write their own code)."""
    opt = "/Od" if cfg == "debug" else "/O1"
    inc = "/INCREMENTAL" if cfg == "debug" else "/INCREMENTAL:NO"
    out = f"smc_harness_{cfg}.exe"
    r = runbat("ml.bat", [f'ml64 /nologo /c /Fo TP.obj /Fl"TP.lst" /Sa "{ROOT / "SelfModTamper/TP.asm"}"'])
    if r.returncode:
        print(r.stdout[-1500:], r.stderr[-800:])
        return r.returncode
    cl = (f'cl /nologo /EHsc /permissive- {opt} /MD /DUNICODE /D_UNICODE /D_CONSOLE /DNDEBUG /I "{VC / "include"}" "{ROOT / "validation/native/smc_harness.cpp"}" '
          f'TP.obj /Fe:{out} /link {inc} /SECTION:.text,RWE /LIBPATH:"{VC / "lib"}" asmjit.lib kernel32.lib user32.lib Mincore.lib Winmm.lib psapi.lib')
    r = runbat("cl.bat", [cl])
    if r.returncode:
        print(r.stdout[-2500:], r.stderr[-800:])
        return r.returncode
    shutil.copy(VC / "bin/asmjit.dll", B / "asmjit.dll")
    return 0


def prefix_release() -> dict:
    """Release harness built from the product source as of the last commit before R12 (HEAD at call time must still hold the
    pre-fix file, i.e. call before committing the fixes, or set REF to that commit): L03 predicts C emulation != asm kernel."""
    ref = __import__("os").environ.get("PREFIX_REF", "HEAD")
    pre = B / "prefix"
    pre.mkdir(exist_ok=True)
    src = subprocess.run(["git", "show", f"{ref}:SelfModTamper/SelfModTamper.cpp"], cwd=ROOT, capture_output=True).stdout
    (pre / "SelfModTamper.cpp").write_bytes(src)
    cl = (f'cl /nologo /EHsc /permissive- /O1 /MD /DUNICODE /D_UNICODE /D_CONSOLE /DNDEBUG /DPRODUCT_CPP=\\"{(pre / "SelfModTamper.cpp").as_posix()}\\" '
          f'/I "{VC / "include"}" "{ROOT / "validation/native/smc_harness.cpp"}" TP.obj /Fe:pre_release.exe /link /INCREMENTAL:NO /SECTION:.text,RWE '
          f'/LIBPATH:"{VC / "lib"}" asmjit.lib kernel32.lib user32.lib Mincore.lib Winmm.lib psapi.lib')
    rec = {"ref": ref}
    r = runbat("clp.bat", [cl])
    rec["build_ok"] = r.returncode == 0
    if r.returncode == 0:
        r = subprocess.run([str(B / "pre_release.exe"), "--text"], cwd=B, capture_output=True, text=True)
        rec["text"] = {"exit": r.returncode, "output": r.stdout[-1500:]}
    return rec


def probes(cfg: str) -> dict:
    """L07: qword counts n with 148 | n crash the unrolled asm kernels; neighbours and the C emulation do not."""
    out = {}
    for n in (148, 149, 296, 297, 592):
        for k in ("TPCompLoop", "gen_asm", "TPCompCLoop"):
            r = subprocess.run([str(B / f"smc_harness_{cfg}.exe"), "--probe", str(8 * n), k], cwd=B, capture_output=True, text=True)
            out[f"n={n} {k}"] = r.returncode
    return out


def acceptance() -> int:
    """Build both configurations and run the Lean-vector replay and the introspective differential on each."""
    results = {}
    for cfg in ("debug", "release"):
        rc = build(cfg)
        rec = {"build_ok": rc == 0}
        if rc == 0:
            for mode, args in (("vectors", ["--vectors", str(ROOT / "validation/native/vectors.txt")]), ("text", ["--text"])):
                r = subprocess.run([str(B / f"smc_harness_{cfg}.exe")] + args, cwd=B, capture_output=True, text=True)
                rec[mode] = {"exit": r.returncode, "output": r.stdout[-3000:]}
        if rc == 0:
            rec["probe_L07"] = probes(cfg)
        results[cfg] = rec
        print(cfg, json.dumps({k: (v if k == "build_ok" else v.get("exit", v)) for k, v in rec.items()}))
    results["prefix_release"] = prefix_release()
    (ROOT / "validation/native/acceptance.json").write_text(json.dumps(results, indent=1) + chr(10))
    return 0


def main() -> int:
    if "--acceptance" in sys.argv:
        return acceptance()
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
    (ROOT / "validation/layout/dyn_x64.json").write_text(json.dumps(out) + chr(10))
    print("dyn_x64.json", len(data), out["printed"])
    return 0


sys.exit(main())
