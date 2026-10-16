r"""Generate lean/errata/ERRATA.md and lean/errata/smctamper-2026-errata.tex from lean/errata/edits.json (paper-only errata
against arXiv:2604.12407v1; code fixes are not errata and are not listed).  Usage: python validation/make_errata.py"""
import json, textwrap
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
BS = chr(92)
UNI = {"≥": "$" + BS + "ge$", "≤": "$" + BS + "le$", "·": "$" + BS + "cdot$", "→": "$" + BS + "to$", "×": "$" + BS + "times$",
       "∀": "$" + BS + "forall$", "∃": "$" + BS + "exists$", "∈": "$" + BS + "in$", "≠": "$" + BS + "ne$", "≈": "$" + BS + "approx$",
       "–": "--", "—": "---", "‘": "`", "’": "'", "“": "``", "”": "''", "²": "$^2$", "∧": "$" + BS + "wedge$", "⊆": "$" + BS + "subseteq$"}


def esc(s):
    s = s.replace(BS, "@@BS@@")
    for a in "&%$#_{}":
        s = s.replace(a, BS + a)
    s = s.replace("^", BS + "^{}").replace("~", BS + "~{}")
    for k, v in UNI.items():
        s = s.replace(k, v)
    return s.replace("@@BS@@", BS + "textbackslash{}")


def tt(s):
    """Quoted TeX source: typewriter, breakable at the characters that may start a new line."""
    t = esc(s.strip().replace("\n\n", " // ").replace("\n", " "))
    return BS + "texttt{" + t + "}"


CLS = {"formal": "Lean", "mechanical": "listing", "editorial": "editorial"}
HEAD = r"""\documentclass[9pt,twocolumn]{article}
\usepackage[a4paper,margin=1.5cm]{geometry}
\usepackage[T1]{fontenc}
\usepackage{lmodern,microtype,enumitem,url}
\usepackage[hidelinks]{hyperref}
\setlist{nosep,leftmargin=0pt,labelsep=0pt,itemsep=2pt}
\setlength{\columnsep}{0.6cm}\setlength{\parindent}{0pt}\setlength{\parskip}{1pt}
\sloppy\emergencystretch=3em
\title{\vspace{-1.2cm}Errata and model clarifications --- \emph{Tamper-Proofing with Self-Modifying Code}}
\author{Errata to G.~Morse and T.~Kozsik, arXiv:2604.12407v1}
\date{}
\begin{document}
\maketitle
\small
\noindent Each item quotes the TeX source of arXiv:2604.12407v1 exactly (\emph{before}), gives the replacement (\emph{after}), a one-sentence
reason and its basis.  \emph{Lean}: proved in the accompanying Lean development (declaration names given); \emph{listing}: checked against
assembled objects or native runs (evidence, not proof); \emph{editorial}: an unambiguous internal inconsistency or a primary source.
Page numbers refer to the arXiv v1 PDF.  Items marked \emph{open} await the authors' confirmation and are not applied.
\section*{Corrections}
\begin{enumerate}[label=]"""


def main():
    d = json.loads((ROOT / "lean/errata/edits.json").read_text(encoding="utf-8"))
    out, md = [HEAD], ["# Errata and model clarifications — Tamper-Proofing with Self-Modifying Code", "",
                       "Against arXiv:2604.12407v1. Generated from `edits.json` by `validation/make_errata.py`.", ""]
    appendix = []
    for e in d["edits"]:
        cls = CLS[e["class"]]
        open_ = e["status"] != "confirmed"
        tag = cls + (", open" if open_ else "")
        long_after = len(e["after"]) > 900
        refs = ""
        if e.get("lean_refs"):
            refs = " " + BS + "emph{Lean:} " + ", ".join(BS + "texttt{%s}" % esc(r.replace("SmcTamper.", "")) for r in e["lean_refs"]) + "."
        after_tex = ("see Appendix (full replacement of the section)." if long_after else tt(e["after"]) + ".")
        if long_after:
            appendix.append((e["id"], e["after"]))
        out.append(BS + "item " + BS + "textbf{%s} (p.~%s, %s; %s). Before: %s After: %s %s%s %s" % (
            e["id"], e["page"], esc(e["location"]), tag, tt(e["before"]) + ".", after_tex, esc(e["reason"]), refs,
            (BS + "emph{Basis:} " + esc(e["evidence"]) + ".") if False else ""))
        md += ["## %s — %s (p. %s; %s; %s)" % (e["id"], e["location"], e["page"], tag, e["confidence"]), "",
               "**Before:**", "", "```tex", e["before"].strip(), "```", "", "**After:**", "", "```tex", e["after"].strip(), "```", "",
               "**Reason:** " + e["reason"], "", "**Evidence:** " + e["evidence"], "", "**Source:** " + e["source"], ""]
        if e.get("lean_refs"):
            md += ["**Lean:** " + ", ".join("`%s`" % r for r in e["lean_refs"]), ""]
    out.append(BS + "end{enumerate}")
    for i, a in appendix:
        out.append(BS + "onecolumn" + BS + "section*{Appendix: replacement text for %s}" % i)
        out.append(BS + "begin{small}" + BS + "begin{verbatim}" + "\n" + "\n".join(textwrap.fill(l, 100, subsequent_indent="  ", break_long_words=False) if l.strip() else "" for l in a.strip().splitlines()) + "\n" + BS + "end{verbatim}" + BS + "end{small}")
    out.append(BS + "end{document}")
    (ROOT / "lean/errata/smctamper-2026-errata.tex").write_text("\n".join(out) + "\n", encoding="utf-8")
    (ROOT / "lean/errata/ERRATA.md").write_text("\n".join(md) + "\n", encoding="utf-8")
    print("items", len(d["edits"]), "appendix", [i for i, _ in appendix])


main()
