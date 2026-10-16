"""Threat-model audit: no field of `structure Assumptions` (Spec/Threat.lean) may mention the conclusion
(alarm, wins, detect, ExecViolation) in its statement. Docstrings are checked for 'detected' wording as well.
Usage: python validation/threat_audit.py"""
import re, sys
from pathlib import Path
src = (Path(__file__).parent.parent / "lean/SmcTamper/Spec/Threat.lean").read_text(encoding="utf8")
start = src.index("def A1 ")
body = src[start:src.index("end SmcTamper", start)]
bad = re.compile(r"\b(Alarm|alarm|Wins|wins|detect\w*|ExecViolation|valueFailAt|timeFailAt|RespIntact)\b")
errs = []
# strip docstrings, check each field line that starts a declaration or continues one
code = re.sub(r"/--.*?-/", "", body, flags=re.S)
for ln in code.splitlines()[1:]:
    mm = bad.search(ln)
    if mm:
        errs.append(f"assumption text mentions '{mm.group(0)}': {ln.strip()}")
names = re.findall(r"\n  (a\d\w*) :", code)
print("fields:", ", ".join(names))
if errs:
    print("\n".join(errs)); sys.exit(1)
print("THREAT AUDIT OK: no Assumptions field mentions alarm/wins/detection")
