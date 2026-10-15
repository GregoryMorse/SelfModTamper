"""Run one scratch Lean file under the memory guard: python validation/lean_scratch.py <file.lean> (imports resolve against the built library)."""
import sys as _s; _s.stdout.reconfigure(encoding="utf-8", errors="replace")
import subprocess, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
BIN = Path.home() / ".elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean.exe"
r = subprocess.run([sys.executable, str(ROOT / "validation/limited_run.py"), "--cwd", str(ROOT / "lean"), "--",
                    str(BIN), str(Path(sys.argv[1]).resolve())], capture_output=True, text=True, encoding="utf-8", errors="replace")
print(r.stdout[-12000:], r.stderr[-2000:])
sys.exit(r.returncode)
