"""asmjit for the validation scripts that call cl.exe directly: the pinned, hash-checked sources are fetched once into build/deps/asmjit
by cmake/fetch_asmjit.cmake (the same pin as cmake/asmjit.cmake and the Visual Studio project) and compiled together with the program."""
import shutil
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DEST = ROOT / "build/deps/asmjit"


def cmake_exe() -> str:
    found = shutil.which("cmake")
    if found:
        return found
    vswhere = Path(r"C:\Program Files (x86)\Microsoft Visual Studio\Installer\vswhere.exe")
    out = subprocess.run([str(vswhere), "-latest", "-property", "installationPath"], capture_output=True, text=True).stdout.strip()
    return str(Path(out) / r"Common7\IDE\CommonExtensions\Microsoft\CMake\CMake\bin\cmake.exe")


def cl_args() -> str:
    """cl.exe arguments (defines, include path, asmjit sources) to put before /link."""
    subprocess.run([cmake_exe(), f"-DDEST={DEST}", "-P", str(ROOT / "cmake/fetch_asmjit.cmake")], check=True)
    src = DEST / "src"
    files = sorted((src / "asmjit/core").glob("*.cpp")) + sorted((src / "asmjit/x86").glob("*.cpp"))
    return "/DASMJIT_STATIC /DASMJIT_NO_FOREIGN " + f'/I "{src}" ' + " ".join(f'"{f}"' for f in files)
