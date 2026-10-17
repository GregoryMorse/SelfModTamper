# Author questions

Asked in R1 (2026-10-15) and answered:

* P05: the 2022 measurement code is the repository code -> P05 (Table 6 row labels) and P05.2 (timed-interval contents) confirmed.
* P07: correct the CMP latency to 1 (uops.info) -> P07 confirmed (RCP cells untouched: AsmGrid unreadable).
* L06: the commented-out segment in TP.asm encloses TPComp only; reconcile without changing behaviour -> comment only.
* Table 1 AMD column: the author does not remember the exact source and asked for primary-source research;
  if it is not in the manual it is an erratum. Research notes and outcome: `PAPER_MAP.md` (R-class table) and P14 in `edits.json`.

Still to ask: repository tag name (suggested `palomar-v1`), in R15/R16.

* WinRing0 reference (not an erratum, for the author): the paper (Section on Windows/Linux access control) cites the OpenLibSys.org manual page for WinRing0.
  The page still resolves, and "a signed kernel driver such as WinRing0" is accurate, so no `confirmed` item exists. Suggestion for the author's other texts and
  v2: also cite the open-source repository the development now builds from (github.com/GermanAizek/WinRing0, pinned commit d567440), since the signed
  1.2.0 binary is no longer downloadable from openlibsys.org. Apply only if the author agrees.

