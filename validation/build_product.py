"""Compile the benchmark product (SelfModTamper.cpp + TP.asm) from a source tree into an output directory, with cl.exe and ml64,
the asmjit sources fetched into build/deps (validation/asmjit_dep.py) and the flags of the Release|x64 project (/O2, /MD, /SECTION:.text,RWE).

  python validation/build_product.py <source-root> <out-dir>

Used by validation/winring0_test.py to build the post-fix product (this tree) and the pre-fix product (a git worktree of the commit
before the R12 fixes), so that both can be run side by side on the same machine.  Not a replacement for the Visual Studio solution."""
import shutil, subprocess, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
VSWHERE = Path(r"C:\Program Files (x86)\Microsoft Visual Studio\Installer\vswhere.exe")
sys.path.insert(0, str(Path(__file__).resolve().parent))
import asmjit_dep  # noqa: E402
ASM = asmjit_dep.cl_args()


def vcvars() -> Path:
    out = subprocess.run([str(VSWHERE), "-latest", "-property", "installationPath"], capture_output=True, text=True).stdout.strip()
    return Path(out) / r"VC\Auxiliary\Build\vcvarsall.bat"


def build(src: Path, out: Path) -> int:
    out.mkdir(parents=True, exist_ok=True)
    bat = out / "build.bat"
    bat.write_text("\r\n".join([
        "@echo off", f'call "{vcvars()}" x64 >nul',
        f'ml64 /nologo /c /Fo TP.obj /Fl"TP.lst" /Sa "{src / "SelfModTamper/TP.asm"}"',
        "if errorlevel 1 exit /b 1",
        f'cl /nologo /EHsc /permissive- /O2 /MD /DUNICODE /D_UNICODE /DNDEBUG /D_CONSOLE {ASM} '
        f'"{src / "SelfModTamper/SelfModTamper.cpp"}" TP.obj /Fe:SelfModTamper.exe /link /INCREMENTAL:NO /SECTION:.text,RWE '
        f'kernel32.lib user32.lib advapi32.lib Mincore.lib Winmm.lib psapi.lib',
    ]) + "\r\n")
    r = subprocess.run(["cmd", "/c", str(bat)], cwd=out, capture_output=True, text=True, stdin=subprocess.DEVNULL)
    if r.returncode:
        print(r.stdout[-3000:], r.stderr[-1000:])
        return r.returncode
    return 0


if __name__ == "__main__":
    sys.exit(build(Path(sys.argv[1]).resolve(), Path(sys.argv[2]).resolve()))
