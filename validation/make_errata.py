r"""Generate lean/errata/selfmodtamper-2019-errata.tex from lean/errata/edits.json.
Usage: python validation/make_errata.py [L01=hash ...]"""
import json, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
BS = chr(92)

def esc(s):
    s = s.replace(BS, "@@BS@@")
    for a in "&%$#_{}":
        s = s.replace(a, BS + a)
    s = s.replace("^", BS + "^{}").replace("~", BS + "~{}")
    s = s.replace("≥", "$" + BS + "ge$").replace("≤", "$" + BS + "le$").replace("·", "$" + BS + "cdot$")
    return s.replace("@@BS@@", BS + "textbackslash{}")

HEAD = r"""\documentclass[10pt,twocolumn]{article}
\usepackage[a4paper,margin=1.7cm]{geometry}
\usepackage[T1]{fontenc}
\usepackage{lmodern,microtype,enumitem}
\setlist{nosep,leftmargin=1.2em}
\setlength{\columnsep}{0.8cm}
\title{\vspace{-1cm}Errata and model clarifications --- \emph{Self-Spectre, Write-Execute and the Hidden State}}
\author{Errata to G.~Morse, Tatra Mt.\ Math.\ Publ.\ \textbf{73} (2019), 131--144, DOI 10.2478/tmmp-2019-0010}
\date{}
\begin{document}
\maketitle
\small
\noindent Page numbers refer to the published version. Items marked \emph{Lean} are proved in the accompanying
formalization (\texttt{lean/}); items marked \emph{listing} are checked against the assembled MASM objects
(evidence, not proof); items marked \emph{editorial} are corrections of the text.
\section*{Corrections to the text}
\begin{enumerate}[label=]"""

def main():
    hashes = dict(a.split("=") for a in sys.argv[1:] if "=" in a)
    d = json.loads((ROOT / "lean/errata/edits.json").read_text(encoding="utf-8"))
    out = [HEAD]
    for e in d["edits"]:
        cls = {"formal": "Lean", "mechanical": "listing", "editorial": "editorial"}[e["class"]]
        refs = ""
        if e.get("lean_refs"):
            refs = r" \emph{Lean:} " + ", ".join(r"\texttt{%s}" % esc(r) for r in e["lean_refs"]) + "."
        out.append(r"\item \textbf{%s} (p.~%s, %s; %s) Replace ``%s'' by ``%s''.%s" % (
            e["id"], e["page"], esc(e["location"]), cls, esc(e["before"]), esc(e["after"]), refs))
    out.append(r"\end{enumerate}")
    out.append(r"\section*{Code supplement}")
    out.append(r"The accompanying sources were corrected by minimal diffs (\texttt{lean/errata/minimal.diff}):")
    items = []
    for c in d["code"]:
        h = hashes.get(c["id"])
        items.append(r"\textbf{%s} \texttt{%s}: %s%s" % (c["id"], esc(c["file"]), esc(c["fix"]),
                     (" (commit %s)" % h) if h else ""))
    out.append(r"\begin{itemize}" + "\n" + "\n".join(r"\item " + i for i in items) + "\n" + r"\end{itemize}")
    out.append(r"\end{document}")
    (ROOT / "lean/errata/selfmodtamper-2019-errata.tex").write_text("\n".join(out) + "\n", encoding="utf-8")

main()
