"""CI axiom audit: import SmcTamper (all modules); every constant declared in a
SmcTamper.* or PalomarSMT.* module may depend only on propext, Quot.sound, Classical.choice
(`sorryAx`, `Lean.ofReduceBool`, custom axioms count as violations). Run from the repository root
after `lake build`:  python3 validation/ci/axioms.py   (uses `lake env lean` in lean/)."""
import subprocess, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[2]
TEMPLATE = """import Lean.Util.CollectAxioms
import Lean.CoreM
import SmcTamper
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
          if !(okAx.contains a) then bad := bad.push s!"{name} uses {a}"
  IO.println s!"AUDIT declarations={n} violations={bad.size}"
  for b in bad do IO.println b
"""
def main():
    f = ROOT / "lean" / "AxiomAuditCI.lean"
    f.write_text(TEMPLATE, encoding="utf-8")
    try:
        r = subprocess.run(["lake", "env", "lean", f.name], cwd=ROOT / "lean", capture_output=True, text=True)
    finally:
        f.unlink()
    print(r.stdout, r.stderr[-2000:])
    ok = r.returncode == 0 and "AUDIT" in r.stdout and "violations=0" in r.stdout
    sys.exit(0 if ok else 1)
main()
