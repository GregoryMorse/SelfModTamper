# Selected Palomar statement

`PalomarSMT.mathematical_result` (Challenge: one deliberate `sorry`; Solution: no holes) is the conjunction of four result
definitions in `SmcTamper/Spec/Paper.lean`. They formalize the threat-model results that replace Section 10 of Gregory Morse and
Tamás Kozsik, *Tamper-Proofing with Self-Modifying Code* (arXiv:2604.12407v1), as corrected by the errata in `errata/` (P01-P13;
P14, the AMD cells of Table 1, was checked against AMD primary documents and is withdrawn). The Harvard/von Neumann observation of
Sections 1 and 10 (C01, C02) is proved in the development (`SmcTamper.Paper.harvard_separation`) but is **not** selected: it is a
general noninterference fact about observation-preserving simulation and its time bound assumes the per-read charge it uses.

`Challenge.lean` is generated mechanically by `validation/make_challenge.py` from the Spec modules reachable from `Spec/Paper.lean`,
with proofs removed and declarations that the five statements do not mention pruned. It imports nothing (Lean core only), so
Challenge and development cannot drift; CI runs `make_challenge.py --check`. `Solution.lean` imports `SmcTamper.Paper`, which proves
each definition from the development's theorems. All proofs use only `propext`, `Quot.sound`, `Classical.choice`
(`validation/ci/axioms.py` audits every `SmcTamper.*` and `PalomarSMT.*` declaration). `Challenge.lean` is about 800 lines and 38 KB:
under the hard limit (1000 lines, 100 KiB) and over the preferred one (300 lines, 32 KiB); the excess is the x86-64 instruction model
that the kernel state of the checksum pulls in.

| Selected declaration | Meaning and scope | Paper / ledger |
| --- | --- | --- |
| `SmcTamper.Paper.SecurityTheorem` | T1. For every system, cost contract, adversary level, timer source and timeline that is well-formed (`WF`) and satisfies the structural assumptions A1-A8, the adversary does not execute a modified protected byte without an effective alarm (`¬ Wins`). An effective alarm needs a unit with a response code (at least one byte, none ever modified) and a value mismatch or a **positive** number `k` of consecutive timing failures; A6 includes `0 < k`, A7 includes that every unit has a response byte. | §10, C46, C50, C56 |
| `SmcTamper.Paper.AssumptionsNecessary` | T3. For each of the eleven assumptions (A1, A2 coverage / code / connectivity / intact unit, A3, A4, A5, A6, A7, A8) there is a well-formed system satisfying all the others in which the adversary wins and that one fails. | §10, C46, C49-C52, C54-C56 |
| `SmcTamper.Paper.MediationTheorem` | T2. In a faithful split-view run every iteration with a non-zero toggle (apart from the last) is mediated, and under A3 and A5 a faithful mediated check with such an iteration is a timing failure. It does not say that every split-view attack is detected (see THREAT_MODEL section 3). | §1, §10 A1, C49 |
| `SmcTamper.Paper.LevelMatrix` | T4. Below L2 with the inline timer A1, A4, A5 hold; L1 with the OS timer API (A5 removed), L2 (A5, and A1) and L4 (A4) each admit a winning adversary against a system that satisfies every other assumption (`OthersHold`, as in T3), so the win is due to that level's capability alone. | §1, §10, C53 |

## Model boundaries (read before relying on the statement)

* The system is **abstract**: units with regions and code, a timeline of write, execution, check, split-view and DMA events, a cost
  contract with lower bounds, and eight structural assumptions. No hardware, operating system, timer or processor is modelled; the
  contract fields (`Cost`, `Level.allows`, `WF`) are hypotheses, never axioms. No theorem says that a real system satisfies them.
* The assumptions are conditions on the timeline and system, never that the attacker is detected (`validation/threat_audit.py`).
* **Not selected** (proved or checked in the development, listed in `PAPER_MAP.md`): the x86-64 model and the static kernel
  emulation (C19-C22), the byte layout of the unrolled kernel against the assembler output (C25, C27, C29), the unrolled kernel at
  Level 1 (C04, C28), the clear contract and its consistency with Table 6 (C12-C14, C24, C36), the timer and noise contract and the
  estimator (C07-C09, C35, C43), the detection predicate, policy and reset (C03, C05, C44, C45), and the data-ratio checks
  (C30-C33, C37, C39). The unrolled kernel is also proved at the instruction level (`unrolled_refines`, relative to the x86-64 model and the conditions of gap G01); the abstract intro event count `I` is not derived (G03).
* Native tests, the MASM listing and AsmJit dumps, and the timing runs of `validation/native/` are evidence, never proof.
