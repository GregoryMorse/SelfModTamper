# Errata policy

Scope: errata against **arXiv:2604.12407v1** (`paper/arxiv-v1/`, PDF `validation/reference/2604.12407v1.pdf`).

1. Only the paper's text, tables, figures and captions can carry errata. Code, README and CITATION fixes are
   **not** errata (the repository has no tagged release; the paper links the repository as a whole) and are
   tracked in `lean/CODE_FIXES.md`.
2. Preserve the published construction and make the smallest local correction that states its intended,
   provable result. `before` is quoted exactly from the TeX source (also found in the PDF text; `before_pdf`
   lists the fragments used to confirm it and the page). Never attribute extraction artifacts to the paper.
3. An item is `confirmed` only when it is certain (a Lean declaration, arithmetic on the paper's own numbers, or a
   primary source) or `inferred` from strong evidence written into `evidence`. Anything else stays
   `ask-author` and is not applied to v2 until answered. `withdrawn` items stay in the file with the reason.
4. Classes: `formal` (cites Lean declarations in `lean_refs`), `mechanical` (cites layout/native evidence),
   `editorial` (primary source or an unambiguous internal inconsistency). Evidence is never called proof.
5. Every item is self-contained (exact quote, correction, one-sentence reason, evidence): the author will map
   the list onto other texts (the dissertation) without this repository's context. The dissertation itself is out
   of scope here.
6. Item ids are stable. A second edit of the same kind in another place gets a suffix (`P04.2`).
   `pending` marks an `after` text that is written in a later round (P11-P13 in R11c).
7. `edits.json` is the single source; `ERRATA.md` and `smctamper-2026-errata.tex` are generated from it
   (`validation/make_errata.py`, R13). Keep the errata PDF at most 3 pages (target 2).
8. The arXiv v2 TeX is v1 plus exactly the `confirmed` edits plus one formal-verification paragraph
   (`validation/apply_edits.py`, R16); `audit_errata.py` checks this.
