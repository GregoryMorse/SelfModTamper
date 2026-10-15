"""Assemble a copy of writeexc.asm (x86 and x64) with listings into validation/.build/<name>/ using
asm_listings.bat (run under the memory guard: python validation/limited_run.py -- python validation/run_listings.py <name> [asm]).
`name` = lst (the published source: `git show 55f0cf5~...` copy) or lstc (the current, corrected source)."""
import shutil, subprocess, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
name = sys.argv[1]; src = Path(sys.argv[2]) if len(sys.argv) > 2 else ROOT / "writeexc.asm"
d = ROOT / "validation/.build" / name; d.mkdir(parents=True, exist_ok=True)
shutil.copy(src, d / "writeexc.asm"); shutil.copy(ROOT / "validation/asm_listings.bat", d / "asm_listings.bat")
r = subprocess.run(["cmd", "/c", str(d / "asm_listings.bat")], cwd=d, stdin=subprocess.DEVNULL, capture_output=True, text=True)
print(r.stdout[-2000:], r.stderr[-2000:], r.returncode)
for f in ("x86.lst", "x64.lst", "x86.obj", "x64.obj"): print(f, (d / f).stat().st_size if (d / f).exists() else "missing")
