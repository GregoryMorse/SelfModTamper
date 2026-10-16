# License check — 2026-10-16

* Project license: **MIT**, declared as `project.license: "MIT"` in `formalization.yaml`. The root `LICENSE` is the MIT text.
  Re-check after the push: `gh api repos/GregoryMorse/SelfModTamper/license`.
* The Lean development under `lean/SmcTamper` is new for this project; `lean/VENDORED.md` records the infrastructure scripts and
  workflows copied from the author's other developments (same author, MIT/CC0), with SHA-256 and edits. No Lean file is vendored.
* Third-party code: the product links AsmJit (zlib license, fetched through vcpkg) and uses the WinRing0 driver interface
  (see README); neither is part of the Lean development or the Palomar statement.
* `paper/arxiv-v1/` and `validation/reference/` hold the arXiv v1 source and PDF, which carry CC BY 4.0 (attributed, unchanged);
  the repository's MIT license does not relicense them. The errata quote short excerpts with page references.
