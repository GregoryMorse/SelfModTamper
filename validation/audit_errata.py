"""Errata audit for lean/errata/edits.json (paper-only errata against arXiv v1).

  --inventory (default): every `before` occurs verbatim (line endings normalised) in the v1 TeX, and every fragment of
      `before_pdf` occurs, after whitespace/hyphenation/ligature normalisation, on one page of the v1 PDF text;
      the page found is reported (`--fill-pages` writes it into `page`).
  --refs: write lean/ErrataRefs.lean (a #check for every declaration named in `lean_refs`).
  --pdf: the errata PDF exists and has at most 3 pages.
"""
import json, re, sys, unicodedata
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
EDITS = ROOT / "lean/errata/edits.json"
TEX = ROOT / "paper/arxiv-v1/SelfModifyingCodeTamperProofingManuscriptUpdated.tex"
PDF_TXT = ROOT / "validation/reference/2604.12407v1.txt"


def norm(s: str) -> str:
    s = unicodedata.normalize("NFKC", s).replace("­", "")
    return re.sub(r"[\s\-]+", "", s)  # hyphens and whitespace are layout noise in the PDF text


def refs() -> int:
    data = json.loads(EDITS.read_text(encoding="utf-8"))
    names = [r for e in data["edits"] for r in e.get("lean_refs", [])]
    root = (ROOT / "lean/SmcTamper.lean").read_text(encoding="utf-8").splitlines()
    mods = [l.split()[-1] for l in root if l.startswith("public import")]
    lines = ["module", ""] + ["import " + m for m in mods] + [""] + ["#check @%s" % n for n in names]
    (ROOT / "lean/ErrataRefs.lean").write_text("\n".join(lines) + "\n", encoding="utf-8")
    print("wrote lean/ErrataRefs.lean,", len(names), "references")
    return 0


def pdf() -> int:
    p = ROOT / "output/pdf/smctamper-2026-errata.pdf"
    n = len(re.findall(rb"/Type\s*/Page[^s]", p.read_bytes()))
    print("errata pdf pages", n)
    return 0 if 1 <= n <= 3 else 1


def inventory(fill: bool) -> int:
    data = json.loads(EDITS.read_text(encoding="utf-8"))
    tex = TEX.read_bytes().decode("utf-8").replace("\r\n", "\n")
    pages = [norm(p) for p in PDF_TXT.read_text(encoding="utf-8").split("\f")]
    bad = 0
    for e in data["edits"]:
        in_tex = tex.count(e["before"]) == 1
        found = []
        frags = e.get("before_pdf") or []
        if frags:
            for i, p in enumerate(pages, 1):
                if all(norm(f) in p for f in frags):
                    found.append(i)
        ok = in_tex and (found or not frags)
        bad += not ok
        if fill and found:
            e["page"] = found[0]
        print("ok  " if ok else "FAIL", e["id"], "tex-once=%s" % in_tex, "pdf-pages=%s" % found, e["status"])
    if fill:
        EDITS.write_text(json.dumps(data, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
    return 1 if bad else 0


def main() -> int:
    if "--refs" in sys.argv:
        return refs()
    if "--pdf" in sys.argv:
        return pdf()
    return inventory("--fill-pages" in sys.argv)


if __name__ == "__main__":
    sys.exit(main())
