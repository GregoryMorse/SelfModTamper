"""Axiom audit: for each given module (default: all locally buildable SmcTamper modules),
import it and check every SmcTamper/PalomarSMT constant uses only the standard axioms.
Usage: python validation/axiom_audit.py [Module ...]"""
import os, subprocess, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent))
import build_modules as B
TEMPLATE = """import Lean.Util.CollectAxioms
import Lean.CoreM
{imports}
open Lean
def okAx : List Name := [`propext, `Quot.sound, `Classical.choice]
#eval show CoreM Unit from do
  let env ← getEnv
  let mut n := 0
  let mut bad : Array String := #[]
  for (name, _) in env.constants.map₁.toList do
    if let some idx := env.getModuleIdxFor? name then
      let root := (env.header.moduleNames[idx.toNat]!).getRoot
      if root == `SmcTamper || root == `PalomarSMT then
        n := n + 1
        let axs ← collectAxioms name
        for a in axs do
          if !(okAx.contains a) then bad := bad.push s!"{{name}} uses {{a}}"
  IO.println s!"AUDIT declarations={{n}} violations={{bad.size}}"
  for b in bad do IO.println b
"""
def main():
    mods = sys.argv[1:] or [str(p.relative_to(B.LEAN).with_suffix("")).replace(os.sep, ".")
                            for p in sorted((B.LEAN / "SmcTamper").rglob("*.lean"))]
    mods = [m for m in mods if not B.needs_mathlib(m)]
    B.main_build = None
    tmp = B.ROOT / "validation/.build"; tmp.mkdir(parents=True, exist_ok=True)
    f = tmp / "AxiomAudit.lean"
    f.write_text(TEMPLATE.format(imports="\n".join("import " + m for m in mods)), encoding="utf-8")
    r = subprocess.run([sys.executable, str(B.ROOT / "validation/limited_run.py"), "--cwd", str(B.LEAN), "--",
        str(B.BIN / "lean.exe"), str(f)], capture_output=True, text=True, encoding="utf-8", errors="replace")
    print(r.stdout[-4000:], r.stderr[-1000:])
    sys.exit(0 if r.returncode == 0 and "violations=0" in r.stdout and "AUDIT" in r.stdout else 1)
main()
