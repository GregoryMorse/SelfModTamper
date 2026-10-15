"""Errata audit.
  (default / --inventory): every `before` occurs in the published text (whitespace/hyphenation/ligature-normalized).
  --refs: write lean/SmcTamper/ErrataRefs.lean-style #check file to validation/.build/ErrataRefs.lean and print the module path.
  --pdf: the errata PDF exists and has at most 3 pages."""
import json, re, sys, unicodedata
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]


def norm(s):
    s = unicodedata.normalize("NFKC", s).replace("­", "")
    s = re.sub(r"-\s*\n\s*", "", s)
    s = re.sub(r"\s+", "", s)  # compare with all whitespace removed: tolerant of pdftotext spacing in code
    return s


def refs():
    data = json.loads((ROOT / "lean/errata/edits.json").read_text(encoding="utf-8"))
    names = [r for e in data["edits"] for r in e.get("lean_refs", [])]
    root_imports = (ROOT / "lean/SmcTamper.lean").read_text(encoding="utf-8").splitlines()
    mods = [l.split()[-1] for l in root_imports if l.startswith("public import") and "MathlibTM0" not in l]
    lines = ["module", ""] + ["import " + m for m in mods] + [""] + ["#check @SmcTamper.%s" % n for n in names]
    out = ROOT / "lean/ErrataRefs.lean"
    out.write_text(chr(10).join(lines) + chr(10), encoding="utf-8")
    print("wrote", out, len(names), "references")


def pdf():
    p = ROOT / "output/pdf/selfmodtamper-2019-errata.pdf"
    n = len(re.findall(rb"/Type\s*/Page[^s]", p.read_bytes()))
    print("pages", n)
    sys.exit(0 if 1 <= n <= 3 else 1)


def main():
    if "--refs" in sys.argv: return refs()
    if "--pdf" in sys.argv: return pdf()
    data = json.loads((ROOT / "lean/errata/edits.json").read_text(encoding="utf-8"))
    pages = (ROOT / "validation/reference/tmmp-2019-0010.txt").read_text(encoding="utf-8").split("\f")
    normed = [norm(p) for p in pages]
    bad = 0
    for e in data["edits"]:
        want = norm(e["before"])
        hit = [131 + i for i, p in enumerate(normed) if want in p]
        ok = bool(hit)
        bad += not ok
        print("ok  " if ok else "FAIL", e["id"], "claimed p%s found %s" % (e["page"], hit))
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
