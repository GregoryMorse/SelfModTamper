# Gap register (single list of everything not yet closed)

Created 2026-10-16 at the author's request: record *all* gaps, close them all. Status: `open`, `in progress`, `closed` (with the commit or file),
or `inherent` (cannot be closed by proof; the precise sound statement that replaces it is given). Update this file at every round close; the round
records (`ROUNDS.md`) and `PAPER_MAP.md` point here.

## A. Lean / formalisation

| ID | Gap | Origin | Plan to close | Status |
|----|-----|--------|---------------|--------|
| G01 | R7 skipped: Level-2 (instruction-level) refinement of the unrolled kernel, `unrolled_refines` (C04, C28) | R7 | prove the unrolled interpreter run equals the Level-1 `unrolled_emulation` on the decoded image; reuse X64 step semantics | open |
| G02 | The unrolled kernel's reset claim is argued, not proved (a copy of `reset_restores` for `fullPasses`) | R11a | prove `reset_restores_unrolled` for the 296-unit kernel | open |
| G03 | The intro's executed length `I` is an abstract parameter, not derived | R9 | derive from G01 (Level 2) and the decoded intro bytes | open (depends on G01) |
| G04 | Exact page-granule clear counts: only upper bounds are proved | R9 | exact count by a counting argument on the periodic stream, or record as inherent if the stream depends on `I` | open |
| G05 | `Data/Consistency` for the g = 64 line granule not done | R9 | analogous to the g = 1 / g = 4096 cases | open |
| G06 | C23 `Unrolled/StateBound` (emulator must track more sites as depth grows) | R6 | statement: number of distinct monitored opcode sites grows with unrolling depth | open |
| G07 | C11 finite-set lemma (monitored addresses are `base + const`) is only the base-relative `opOff` | R6 | finite-set lemma over `Finset`-free lists | open |
| G08 | C28 restore, C17 (Table 2 toggle closure), C26 (placeholder sizes) rows still marked todo in PAPER_MAP although parts exist | R2, R5 | R14 audit: map each to its Lean theorem or prove | open (audit) |
| G09 | Emulation cost is a contract field (`emulLB`); no formal instance links it to `harvard_time_bound` | R11b | prove `emulLB x ≤ interp time` for a Harvard-interpreter emulation of the unit, as an instance of the field | open |
| G10 | T2 does not give "T1 holds without A1": split reads of non-executed bytes are invisible | R11c | **inherent** to the model: restate T2 as in THREAT_MODEL §3 (done); optionally add a variant assumption "every protected byte is code executed by an SMC unit" and prove T1 for it | inherent (scoped); variant open |
| G11 | Necessity witnesses for A2 `code ⊆ prot`, A2 strong connectivity, A7 | R11c | two-unit system `mk2Sys` and tail timelines | open |
| G12 | 3-quadword forgery theorem and 2-quadword impossibility for the single-site kernel (A8) | R11c | formalise the construction (toggles 0/1/4/5 via r = 1, 2^63+1, 0, 2^63) and the predecessor lemma | open |
| G13 | Unit-reset assumption for WF "honest" path uses the Level-1 kernel only | R11b | link `viewValue` to the unrolled kernel after G01/G02 | open (depends on G01, G02) |
| G14 | i.i.d. noise model, quantile calibration (R10, R11a) | R10 | optional Bernoulli form; calibration theorem from sample quantiles | open (could) |
| G15 | Level L3 has no events of its own | R11b | either give L3 (hypervisor) its events (EPT mediation) or remove it from the table | open |
| G16 | `Challenge.lean`, `Spec/Paper.lean` (Props `SecurityTheorem`, `AssumptionsNecessary`), coverage and fidelity audit | R14 | rounds R14 | open |

## B. Platform and source facts (R-class)

| ID | Gap | Plan | Status |
|----|-----|------|--------|
| G20 | P14: AMD MSR C000_0301 and PMCx021 primary source | find AMD64 APM Vol. 2 / PPR text; else ask author | open |
| G21 | Intel SDM: VMX RDTSC exiting / TSC offsetting, EPT execute-only, DR0–DR7 not read from primary text | read SDM Vol. 3C ch. 25/26 and Vol. 3B; record section numbers | open |
| G22 | CR4.TSD fact taken from a secondary mirror | read SDM Vol. 2 RDTSC and Vol. 3A §2.5 | open |
| G23 | Literature roles in THREAT_MODEL §5 come from titles, not from re-reading the papers | read the nine papers' relevant sections or soften the roles | open |
| G24 | P05 provenance of the "SMC Loop" / "Dyn SMC Loop" labels in Tables 4–5 | the pre-fix binary prints "SMC Loop" for the AsmJit kernel and "Dyn SMC Loop" for the static one (L01, confirmed by the pre-fix run: swapped rows are equal within 1%, so the data cannot say); ask the author which order the paper tables used | in progress (author to confirm) |

## C. Code and native (R12)

| ID | Gap | Plan | Status |
|----|-----|------|--------|
| G30 | L01–L06, D01–D03 not applied | R12 | closed (9b5e125) |
| G31 | Lean-generated test vectors for the native kernels (`--vectors`) | R12 | closed: 36 vectors, all five kernels, Debug and Release (`validation/native/acceptance.json`) |
| G32 | Native acceptance: Debug and Release differential tests; Release fails before L03 | R12 | closed (pre-fix Release `--text` fails, post-fix passes) |
| G33 | Native timing consistency with the paper's Tables 4–5 (pattern, not values) on this machine; no driver | R12 | closed after the Debug run: `validation/data/native_runs.json` |
| G34 | L07: the unrolled asm kernels crash when 148 divides the qword count (termination patch assumes next byte 0x48); native confirmation done, guard applied; root-cause fix would change the layout constants (7974, 27, 95) that R5 verified, so it is **deliberately not made**: the Level-2 statement must carry the precondition 148 ∤ n | guard closed; fix declined (record in R15 notes / paper v2 remarks) |
| G35 | Build system: MSBuild solution is authoritative; CMake preset points at VS 2022 generator | R12 | closed: preset defaults to VS 2026, extra VS 2022 preset; the CMake route itself was not exercised |
| G36 | WinRing0 on Windows 11 (vulnerable-driver blocklist, HVCI/memory integrity): MSR path may not load | R12: the product was run unelevated without the driver (timer columns valid, event counters read 0, as in `validation/native/runs/`); loading the driver was not attempted. Author action only: elevated run with the driver, or the PMC route on a machine with the blocklist off | open (author action, optional: timing and clear counts do not enter any Lean statement) |

## D. Release path

| ID | Gap | Plan | Status |
|----|-----|------|--------|
| G40 | R13 errata list generation, `QUESTIONS.md` items | R13 | open |
| G41 | R14 coverage audit (`coverage_audit.py`) | R14 | open |
| G42 | R15 Palomar package; Palomar policy assets not copied; `palomar-full.yml` dispatch needs the author's go-ahead; submission and registration by the author | R15 | open |
| G43 | R16 tag (name to confirm), arXiv v2 manuscript in `paper/` | R16 | open |
| G44 | PAPER_MAP statuses are stale for several rows (R11b/R11c rows still `todo`) | refresh in R14 | open |
