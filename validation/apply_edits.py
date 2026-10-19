"""Build the arXiv v2 manuscript source from v1 (plan D9, errata POLICY item 8).

v2 = v1 TeX + exactly the `confirmed` items of lean/errata/edits.json (P10 is optional and applied)
   + one "Formal verification" section and one "AI assistance disclosure" section (before the bibliography)
   + one bibliography entry for the formalization.

Writes paper/SelfModifyingCodeTamperProofingManuscriptUpdated.tex, paper/biblio.bib and paper/v1-v2.diff.
`--check` verifies that the files on disk are exactly what this script produces.
"""
import difflib
import re
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
V1 = ROOT / "paper/arxiv-v1"
OUT = ROOT / "paper"
NAME = "SelfModifyingCodeTamperProofingManuscriptUpdated.tex"
EDITS = ROOT / "lean/errata/edits.json"

COMMIT = "0a48a85e0f1884a50c6abdcf8617bd315a6b59c2"
REPO = "https://github.com/GregoryMorse/SelfModTamper"
ENTRY = "PALOMAR-2026-10-18-000004"
ENTRY_URL = "https://palomar-registry.org/entry?id=PALOMAR-2026-10-18-000004\\&version=1"
TAG = "palomar-v1"

FORMAL = r"""
\section{Formal verification}\label{sec:formal}

\begin{sloppypar}
The threat model of Section~\ref{sec:assumptions} is formalised and machine-checked in Lean~4 (toolchain \texttt{leanprover/lean4:v4.35.0-rc3}, no Mathlib)~\cite{smctamper-lean}.
The Lean development is registered with the Palomar registry as entry \texttt{PALOMAR-2026-10-18-000004}, version~1, and is published at \url{https://github.com/GregoryMorse/SelfModTamper}, release tag \texttt{palomar-v1}, commit \path{0a48a85e0f1884a50c6abdcf8617bd315a6b59c2}.
The registered statement consists of the four results T1--T4 of Section~\ref{sec:assumptions}, proved for the abstract model defined there (checksum units, adversary levels L0--L4, assumptions A1--A8, and a cost contract).
Platform behaviour, that is, what a privilege level can do, which timing bounds hold, and what an operating system or processor provides, enters only as explicit fields of that model, not as a proved fact about real hardware or software.
The same repository contains Lean checks of further statements of this paper (layout and timing arithmetic, checked as consistency of the reported numbers; the separation of Harvard and von Neumann architectures; a forgery of the checksum from three modified quadwords) that are not part of the registered statement.
The repository file \texttt{lean/PAPER\_MAP.md} assigns each claim of the paper to a Lean declaration, a cited platform fact, or the class of observation.
The Lean development is supporting material: the paper's measurements and listings do not depend on it, and what it checks is limited to the statements described above.
The listings, native tests and measurements are evidence for the implementation, not proofs.
The corrections to the text of the first version that this version makes were found while formalising the statements.
\end{sloppypar}
"""

AI = r"""
\section*{AI assistance disclosure}

Anthropic Claude Opus 5.5 in high thinking mode and Anthropic Claude Sonnet 5.5 in medium thinking mode, used through the Claude Code command-line agent, assisted with the Lean formalization (statement drafting, proof development and proof repair), the validation scripts, the repository documentation, the comparison of the first version with the formalization, and the drafting of the corrections made in this version.
The Lean kernel checks the proofs; the author reviewed the formal statements, the corrections to the text and this manuscript, and assumes full responsibility for the final work.
"""

BIB = r"""

@misc{smctamper-lean,
  author = {Gregory Morse and Tam\'{a}s Kozsik},
  title = {Tamper-proofing with self-modifying code: threat model, security and necessity of the assumptions},
  howpublished = {Lean~4 development, Palomar registry entry PALOMAR-2026-10-18-000004, version~1; \url{https://github.com/GregoryMorse/SelfModTamper}, tag \texttt{palomar-v1}, commit \path{0a48a85e0f1884a50c6abdcf8617bd315a6b59c2}},
  year = {2026}
}
"""


PAGES = 14  # verified against the built PDF by the arXiv audit (ARXIV_AUDIT.md)


def metadata(tex):
    """Canonical arXiv metadata region (skill: arxiv-submission-auditor); the abstract is expanded to ASCII on one line."""
    a = tex[tex.index(r"\begin{abstract}") + len(r"\begin{abstract}"):tex.index(r"\end{abstract}")]
    a = re.sub(r"\\emph\{([^}]*)\}", r"\1", a).replace("---", " - ").replace("~", " ")
    a = " ".join(a.split())
    assert a.isascii() and len(a) <= 1920 and "\\" not in a, len(a)
    return "\n".join([
        r"\iffalse", "ARXIV-METADATA-BEGIN",
        "Title: Tamper-Proofing with Self-Modifying Code",
        r"Authors: Gregory Morse (E\"otv\"os Lor\'and University), Tam\'as Kozsik (E\"otv\"os Lor\'and University)",
        "Abstract: " + a,
        "Comments: %d pages, 5 figures, 6 tables. Lean 4 formalization (Palomar entry PALOMAR-2026-10-18-000004 v1): %s , tag %s" % (PAGES, REPO, TAG),
        "Subjects: Cryptography and Security (cs.CR); Logic in Computer Science (cs.LO)",
        "MSC classes: 68M25 (Primary) 68M20, 68N30, 68Q60, 68V15 (Secondary)",
        "ACM classes: D.4.6; D.4.8; D.2.0; F.3.1",
        "Report number: N/A -- leave blank", "Journal reference: N/A -- leave blank", "DOI: N/A -- leave blank",
        "License: Creative Commons Attribution 4.0 (CC BY 4.0)",
        "Submitter is author: Yes",
        "External artifacts: GitHub %s ; release/tag %s ; commit %s ; verified 2026-10-18" % (REPO, TAG, COMMIT),
        "AI disclosure: AI assistance disclosure (unnumbered section) -- " + " ".join(AI.replace("~", " ").replace(chr(92) + "section*{AI assistance disclosure}", "").split()),
        "ARXIV-METADATA-END", r"\fi", ""])



def build():
    tex = (V1 / NAME).read_bytes().decode("utf-8")
    crlf = "\r\n" in tex
    tex = tex.replace("\r\n", "\n")
    data = json.loads(EDITS.read_text(encoding="utf-8"))
    applied = []
    for e in data["edits"]:
        if e["status"] != "confirmed":
            continue
        before = e["before"].replace("\r\n", "\n")
        after = e["after"].replace("\r\n", "\n")
        assert tex.count(before) == 1, (e["id"], "before not found exactly once")
        tex = tex.replace(before, after)
        applied.append(e["id"])
    ab = "analysis, a threat model, and deployment guidance for trusted code executing in\nuntrusted environments.\n"
    assert tex.count(ab) == 1
    tex = tex.replace(ab, ab + "The threat model is formalised in Lean~4, relative to an explicit platform contract: the\n"
                      "security theorem, the necessity of each assumption and which assumptions each adversary level\n"
                      "satisfies or breaks are machine-checked, and the development is registered with the Palomar registry.\n")
    # P11 is a standalone erratum; in v2 its pointer goes to the new Formal verification section
    ref = "checked in Lean (Section~\\ref{sec:summary})"
    assert tex.count(ref) == 1
    tex = tex.replace(ref, "checked in Lean (Section~\\ref{sec:formal})")
    marker = "\\bibliographystyle{unsrt}"
    assert tex.count(marker) == 1
    tex = tex.replace(marker, FORMAL.strip("\n") + "\n" + AI.strip("\n") + "\n\n" + marker)
    DOC = "\\begin{document}"
    assert tex.count(DOC) == 1
    tex = tex.replace(DOC, metadata(tex) + DOC)
    bib = (V1 / "biblio.bib").read_bytes().decode("utf-8")
    bcrlf = "\r\n" in bib
    bib = bib.replace("\r\n", "\n")
    bib = re.sub(r"\n@article\{Mankowitz2023,.*?\n\}\n?", "\n", bib, flags=re.S)  # never cited in v1 (unsrt omitted it)
    assert "Mankowitz" not in bib
    for o, n in (("pages={10 pp.-32}", "pages={23--32}"),
                 ("doi = {https://doi.org/10.1016/j.chaos.2007.10.022}", "doi = {10.1016/j.chaos.2007.10.022}")):
        assert bib.count(o) == 1, o
        bib = bib.replace(o, n)  # bibliographic data corrected against Crossref (2026-10-18)
    bib = bib.rstrip("\n") + "\n" + BIB
    if crlf:
        tex = tex.replace("\n", "\r\n")
    if bcrlf:
        bib = bib.replace("\n", "\r\n")
    diff = "".join(difflib.unified_diff(
        (V1 / NAME).read_bytes().decode("utf-8").replace("\r\n", "\n").splitlines(True),
        tex.replace("\r\n", "\n").splitlines(True), "v1/" + NAME, "v2/" + NAME))
    return tex, bib, diff, applied


def main():
    tex, bib, diff, applied = build()
    files = {OUT / NAME: tex.encode("utf-8"), OUT / "biblio.bib": bib.encode("utf-8"), OUT / "v1-v2.diff": diff.encode("utf-8")}
    if "--check" in sys.argv:
        bad = [p.name for p, b in files.items() if not p.exists() or p.read_bytes() != b]
        print("v2 matches v1 + confirmed edits + additions" if not bad else "MISMATCH: " + ", ".join(bad))
        return 1 if bad else 0
    for p, b in files.items():
        p.write_bytes(b)
    print("applied", len(applied), "edits:", " ".join(applied))
    return 0


if __name__ == "__main__":
    sys.exit(main())
