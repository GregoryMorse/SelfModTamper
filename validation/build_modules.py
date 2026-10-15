"""Build SmcTamper modules (and their SmcTamper imports) one at a time with
direct lean.exe under validation/limited_run.py (Lake exceeds the 1.5 GB commit cap).
Usage: python validation/build_modules.py [--force] Module.Name [...]   ('all' = every module)."""
import argparse, os, re, subprocess, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "lean"
OUT = LEAN / ".lake/proof-build/lib/lean"
BIN = Path(os.environ.get("ELAN_HOME", Path.home() / ".elan")) / "toolchains/leanprover--lean4---v4.35.0-rc3/bin"

def path(mod): return LEAN / (mod.replace(".", "/") + ".lean")
def imports(mod):
    text = path(mod).read_text(encoding="utf-8")
    return [m for m in re.findall(r"^(?:public )?import\s+(SmcTamper[\w.]*)", text, re.M)]
def order(mods, seen=None, out=None):
    seen = set() if seen is None else seen; out = [] if out is None else out
    for m in mods:
        if m in seen: continue
        seen.add(m); order(imports(m), seen, out); out.append(m)
    return out
def needs_mathlib(mod):
    if re.search(r"^(?:public )?import\s+Mathlib", path(mod).read_text(encoding="utf-8"), re.M): return True
    return any(needs_mathlib(i) for i in imports(mod))
def stale(mod):
    olean = OUT / (mod.replace(".", "/") + ".olean")
    if not olean.exists(): return True
    t = olean.stat().st_mtime
    return path(mod).stat().st_mtime > t or any((OUT / (i.replace(".", "/") + ".olean")).stat().st_mtime > t for i in imports(mod))
def main():
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    ap = argparse.ArgumentParser(); ap.add_argument("--force", action="store_true"); ap.add_argument("mods", nargs="+")
    a = ap.parse_args()
    mods = [str(p.relative_to(LEAN).with_suffix("")).replace(os.sep, ".") for p in sorted((LEAN / "SmcTamper").rglob("*.lean"))] + ["SmcTamper"] if a.mods == ["all"] else a.mods
    for m in order(mods):
        if needs_mathlib(m):
            print("SKIP (imports Mathlib; exceeds the 1.5 GB local cap, CI-only)", m, flush=True); continue
        if not (a.force or stale(m)): continue
        target = OUT / (m.replace(".", "/") + ".olean"); target.parent.mkdir(parents=True, exist_ok=True)
        print("BUILD", m, flush=True)
        r = subprocess.run([sys.executable, str(ROOT / "validation/limited_run.py"), "--cwd", str(LEAN), "--timeout", "3000", "--",
            str(BIN / "lean.exe"), str(path(m).relative_to(LEAN)), "-o", str(target), "-i", str(target.with_suffix(".ilean"))],
            capture_output=True, text=True, encoding="utf-8", errors="replace")
        print(r.stdout[-6000:], r.stderr[-2000:], flush=True)
        if r.returncode: sys.exit(f"FAILED {m}")
if __name__ == "__main__": main()
