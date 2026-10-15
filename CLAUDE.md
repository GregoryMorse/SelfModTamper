# SelfModTamper — Lean verification of "Tamper-Proofing with Self-Modifying Code"

Goal: Lean-verify every mathematical, algorithmic and quantitative statement of Morse & Kozsik,
arXiv:2604.12407v1 (unconditionally or relative to an explicit platform contract), fix the legacy code,
produce a paper-only errata list, get the development registered on Palomar, then tag the registered
commit and produce an arXiv v2 manuscript that states its Lean verification, Palomar entry and tag.

**Every session:** read `lean/FORMALIZATION_PLAN.md` §0–§4, then only the current round's section
(state and handoff notes: `lean/ROUNDS.md`). Decisions in plan §2 are settled; ask the user before
deviating. Do not browse `../selfspectre` or `../smcTuring` beyond the paths the plan names.

**Current round: R2** (R0, R1 done). Update this line at each round close.

## Hard rules

- Run every build/test serially through `python validation/limited_run.py -- <cmd>` (1.5 GB aggregate
  cap, Lean `-M768 -j1`) once R0 has copied it. A capped failure is a failed check; never bypass the
  guard. Do not kill unrelated processes.
- No SSH/remote servers. Cold full builds and Palomar runs use GitHub Actions.
- Pin: Lean `leanprover/lean4:v4.35.0-rc3`, no Mathlib (plan D4). Do not change either without asking.
- No `sorry`/`admit` (except `lean/Challenge.lean`), no `axiom`, `native_decide`, `bv_decide`,
  `Lean.ofReduceBool`, `unsafe`. Only `propext`, `Quot.sound`, `Classical.choice` may appear.
- Windows and the CPU are black boxes: platform behaviour enters only as fields of the contract
  structures (plan D2), never as axioms or as claims about real hardware.
- The threat model (§10, plan D11, rounds R11b–R11c) is the crux of the paper. Assumptions must be
  structural, never "the attacker is detected" (`validation/threat_audit.py`). Each one needs a
  necessity witness. Never cut these rounds for budget.
- Statement-level definitions live in `lean/SmcTamper/Spec/` (core imports only, `@[expose]`);
  `Challenge.lean` is generated from them.
- Errata: paper text, tables, figures and captions only, quoted exactly from arXiv v1
  (`paper/arxiv-v1/`, PDF in `validation/reference/`); each item self-contained. Code/README/CITATION
  fixes are **not** errata (no tagged release yet) and go to `lean/CODE_FIXES.md`. Never edit
  `paper/arxiv-v1/`. The dissertation is out of scope: do not read or quote it.
- Evidence (native tests, listings, data fits) is never described as proof. Prose (docstrings, YAML,
  Markdown, the v2 statement) must claim no more than the Lean hypotheses give.
- Economy: one round per session; build only touched modules until round close; three focused attempts
  per obstacle, then narrow the statement and record an open obligation in `lean/PAPER_MAP.md`; at most one
  batched question to the user per round.

## Authorizations (user, 2026-10-15)

- Commits to `main` at green increments and pushes to `origin`: **authorized**. Never force-push; never
  move or delete a tag.
- The arXiv v1 source and PDF (CC BY 4.0) may be committed (plan D9: commit them under `paper/arxiv-v1/`
  and `validation/reference/`).
- Dissertation: out of scope (the author builds a dissertation-wide errata list separately).
- Never write to OneDrive; the v2 manuscript lives in `paper/` and the user uploads it.
- Order: Palomar first, then the repository tag (R16, name confirmed with the user), then the v2 manuscript.
- Dispatching `palomar-full.yml` needs the user's go-ahead (ask in R15). Palomar submission and
  registration are always done by the user; never submit or register.
