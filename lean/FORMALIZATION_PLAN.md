# Tamper-Proofing with Self-Modifying Code: formalization plan

Planner: Claude Opus 5.5, 2026-10-15. Executor: Claude Sonnet 5.5 (medium effort), one round per
session (a round may span sessions, but every session closes at least one numbered step with a green
build). Reviewer and decision owner: Gregory Morse (first author).

**How to use this file.** At the start of every session, read §0–§4 once and then **only the section
of the current round** (state and handoff notes: `lean/ROUNDS.md`). §1 facts are established; do not
re-derive them unless a gate fails. §2 decisions are settled; if one blocks you, stop and ask the user.
Do not browse `../selfspectre` or `../smcTuring` beyond the exact paths named here.

---

## 0. Target

**Paper.** G. Morse, T. Kozsik, *Tamper-Proofing with Self-Modifying Code*, arXiv:2604.12407v1
(submitted 2026-04-14, license CC BY 4.0).

| Artifact | Location | Size | SHA-256 |
|---|---|---|---|
| e-print tarball | `https://arxiv.org/e-print/2604.12407v1` | 28,990 B | `a0799974b290d4dd10e016db14e72b4491b98289dce9d0e9cfdbf314b6f3231b` |
| TeX (top level) | `SelfModifyingCodeTamperProofingManuscriptUpdated.tex` in the tarball | 37,042 B, 696 lines | `79d7261088f2f783776f88c41a3b97b8ba926fad20b709400bcd6917b89c89b5` |
| `biblio.bib` | tarball | 6,869 B | `66bd24c4404721438f4c8b922895dd497bd033bced8e0817fd0fea1d7d624049` |
| `Tamperproof.eps` | tarball | 31,163 B | `2966c03a1e5e9908ddeafa19b60b9c4dfccb08f1bbdefe4cb0556c17d14b0c2c` |
| PDF v1 | `https://arxiv.org/pdf/2604.12407v1` | 188,386 B, 11 pages | `636f8d2a2989160a3437c846fd819cf3fe69c673980578fd456dce701e9ea287` |

The author's working copy `D:\OneDrive\Documents\Projects\ELTE\smctamperproof\SelfModifyingCodeTamperProofingManuscriptUpdated.tex`
is byte-identical to the arXiv TeX (same SHA-256). Never write to OneDrive: the arXiv v2 manuscript is
produced in `paper/` (R16) and handed to the user, who uploads it.

**Dissertation: out of scope (user decision, 2026-10-15).** The author's frozen dissertation contains this
paper as a section. The author will derive a dissertation-wide errata list separately, with another agent,
from the errata lists of all their projects. Do not read, quote or map the dissertation. Consequence: every errata item
here must be **self-contained** (exact v1 quote, corrected text, one-sentence reason, evidence), so that it
can be mapped to other texts without this repo's context.

**What counts as an erratum (user decision, 2026-10-15).** Only statements in the paper's text, tables,
figures and captions. Code, README and CITATION fixes are **not** errata: the repository has no tagged
release, and the paper links only the repository as a whole. They are tracked in `lean/CODE_FIXES.md`. The
first tag is created in R16 on the Palomar-registered commit, so every code fix must land before that commit.

**Sequence (user decision, 2026-10-15):** Lean development → code fixes → errata list → Palomar package
(the user submits and registers) → repository tag → arXiv v2 manuscript that states its Lean verification,
the Palomar entry and the repository tag.

**Artifacts in this repo.** `SelfModTamper/TP.asm` (static kernels `TPComp`, `TPCompLoop`),
`SelfModTamper/SelfModTamper.cpp` (C models `TPCompC`, `TPCompCLoop`, generator `gen_asm`, driver),
`SelfModTamper/func.asm` (text dump of the generated code).

**Float numbering** (source order; R1 confirms against the PDF): Fig. 1 design overview, Fig. 2 static SMC
kernel, Fig. 3 C++ emulation, Fig. 4 AsmJit snippet, Fig. 5 experimental setup output; Table 1 MSR/event
values, Table 2 opcode pattern, Table 3 instruction reference, Table 4 static results, Table 5 dynamic
results, Table 6 machine-clear counts.

**In scope: the whole paper.** Every sentence-level mathematical, algorithmic or quantitative claim gets a
class (D1) and is discharged in Lean, unconditionally or relative to the explicit platform contract
(D2), or as a Lean-checked consistency fact about the reported measurements. Platform facts are cited to
primary sources; pure observation/opinion is listed as such. Nothing about Windows or the CPU is treated as a
white box (D2).

**Final deliverables (definition of done).**
1. `lean/` Lake project: zero `sorry` outside `Challenge.lean`; only `propext`, `Quot.sound`,
   `Classical.choice`; cold CI build + axiom audit green on GitHub.
2. `lean/PAPER_MAP.md` covering every claim C01–C48 (+ any found in R1) with class, declaration or
   source, status; `validation/coverage_audit.py` passing (R14). Only then may README/metadata say
   "the paper's mathematical content is Lean-verified" in the wording fixed by D1.
3. Code and docs fixes L01–L06, D01–D03 as minimal diffs with native acceptance (Debug/Release, R12),
   listed in `lean/CODE_FIXES.md` with commit hashes. Not errata (§0).
4. Errata list (paper only, against arXiv v1): `lean/errata/edits.json` (single source), generated
   `lean/errata/ERRATA.md` (readable on GitHub) and `lean/errata/smctamper-2026-errata.tex` → PDF reviewed
   by the author (R13).
5. Palomar package (`Challenge.lean`, `Solution.lean`, `comparator.json`, `formalization.yaml`,
   `PALOMAR_SEMANTICS.md`, `PALOMAR_SUBMISSION.md`, `PLATFORM_CONTRACT.md`), full mechanical preflight
   passing on an exact public commit (R15). **The user submits and registers; never do it yourself.**
6. After registration (R16): an annotated repository tag on the registered commit, and the arXiv v2
   manuscript `paper/SelfModifyingCodeTamperProofingManuscriptUpdated.tex` with every confirmed erratum
   applied plus a short statement of its Lean verification (D1 wording) naming the Palomar entry and
   version, the repository URL, the tag and the commit; `paper/v1-v2.diff` and
   `output/pdf/smctamper-v1-v2-latexdiff.pdf`. Pristine v1 stays in `paper/arxiv-v1/`. The user uploads v2.

---

## 1. Facts established during planning (do not re-verify unless a gate fails)

**Paper ↔ code map.** Fig. 2 = `TP.asm` `TPComp` (lines 17–48). Fig. 3 = `TPCompC` (`.cpp` 417–439; the
figure omits lines 419–421, where `pTPCompOffset` is computed from the incremental-link jump thunk).
Fig. 4 = the `code_gen` lambda (`.cpp` 214–224). Fig. 5 = the printfs at `.cpp` 228 and 673 plus CPUID
output. `TPCompCLoop` = `.cpp` 452–497. `TP.asm` `TPCompLoop` (52–end) is the `gen_asm` dump assembled
statically (5 NOPs pad page 1; `_TEXT$SMC SEGMENT ALIGN(4096)` is commented out, so the static loop is
**not** page-aligned; the dynamic copy is `memcpy`'d into `VirtualAlloc` memory, which is page-aligned,
`.cpp` 279). Every benchmark variant checksums the EXE `.text` (`base`, `SizeOfRawData`, `.cpp` 376–381),
so the dynamic kernel lies **outside** the checksummed region; `TPCompCLoop` emulates the *static*
`TPCompLoop`.

**Encodings and layout (arithmetic verified).**
* Fig. 2 bytes: `ADC RBX,[RSI]` = `48 13 1E`, `SETS DL` = `0F 98 C2`, `SETP AL` = `0F 9A C0`,
  `SHL AL,2` = `C0 E0 02`, `OR DL,AL` = `0A D0`, `SHL DL,3` = `C0 E2 03`. `$-2-3-3-3-2-3` = `$-16` = the
  ADC opcode byte (the ADC starts at `$-17`; `XOR m8,r8` is RIP-relative `30 15 disp32`, disp = −22).
* `TPComp` opcode offset `0xF` = 3 `USES` pushes + `MOV RSI,RCX` (3) + `LEA RDI,[RSI+RDX]` (4) +
  `XOR RBX,RBX` (3) + `CLC` (1) + REX `48` (1).
* Dynamic unit = 27 B = `0x1B`: `adc rbx,[rcx]` 3, `sets` 3, `setp` 3, `shl al,2` 3, `or dl,al` 2,
  `shl dl,3` 3, `xor [rip+d32],dl` 6, `lea rcx,[rcx+8]` (`48 8D 49 08`) 4.
* `148 = ⌊(4096 − 95)/27⌋`; page 1 = intro 95 + 148·27 = 4091 + 5 NOPs; page-2 unit k (148 ≤ k < 296)
  at 4096 + 27(k − 148). Unit k starts at 95 + rsi(k), rsi(k) = 27k + 5·[k ≥ 148] (the intro's `cmp/jl/add esi,5`).
  `TPCompCLoop` constants: 148, `0x1B`, opcode offsets `0x60` = 95 + 1 and `4096 + 1`.
* Termination patch: `rdi = (0xE9 ^ 0x4808498D48) ^ (disp << 8)` with disp = 7974 − rsi XORs
  `48 8D 49 08 48` (unit k's LEA + next REX) into `E9 disp32`. Its target is 95 + rsi + 23 + 5 + disp =
  **8097 for every k**, the byte after `jmp L0` (page 2 ends at 8092; `jmp L0` is `E9 rel32`). The epilogue
  re-applies the same XOR (involution) via a self-modified displacement (`add [L301-4],esi` / `sub`).
* Fig. 5: `0x7FF7B4521000 + 0x8200 = 0x7FF7B4529200`.

**Placeholder measurement (suspected fragility, R5 confirms).** `gen_asm` measures the intro with
placeholders (127, 127, 127). Two immediates change size between measurement and emission:
`cmp rdi,127` imm8 (4 B) → `cmp rdi,148` imm32 (7 B), and `add esi,−12160` imm32 (6 B) → `add esi,5`
imm8 (3 B); the changes cancel. The 95-byte total holds if AsmJit emits `mov rax,imm` as `48 C7 C0 imm32`
(7 B); with `B8 imm32` (5 B) the total would be 93. Unconfirmed until R5 dumps the generated bytes.

**Flags.** CF = 0 at every ADC/SBB: `CLC` before the first; in `TPComp`, `CMP RDI,RSI` leaves CF = 0
whenever `JG` loops (both addresses < 2^63); in loop units the previous `XOR m8,r8` clears CF. So
ADC ≡ ADD and SBB ≡ SUB, as `TPCompC` assumes. `paritybyte` returns odd parity, so `!paritybyte` = PF.
`op` ∈ {0,1,4,5} ↔ opcodes `13/1B/33/3B` (ADC/SBB/XOR/CMP), op = ((opcode >> 3) & 7) ^ 2; the toggle
`(PF << 2) | SF` keeps op in {0,1,4,5}, so `default: res = 0` is unreachable.

**Code defects found by reading (become L items; confirm in R12).**
* `testFuncs` = {C, TPComp, C Loop, **TPCompF (dynamic)**, **TPCompLoop (static)**} but `strFuncNames`
  = {…, "SMC Loop", "Dyn SMC Loop"}: labels 4/5 are swapped. Present since the initial commit.
* The timed interval (`.cpp` 697–703) contains a `std::cout … << std::endl` and a WinRing0 IOCTL
  (`getSMCCount`) per run. Also present in the initial commit (2026-04-08); whether the 2022 data were
  taken with it is for the author.
* `TPCompC`/`TPCompCLoop` dereference `TPComp+1` as an `E9 rel32` incremental-link thunk. With
  `LinkIncremental=false` (Release `.vcxproj`, CMake Release) `pTPCompOffset` is garbage, so the "precise"
  C emulation silently stops substituting the opcode.
* Loop preconditions: `size ≥ 8` and `8 | size`. If `size mod 2368 ∈ [1,7]` the intro computes index −1
  and writes the JMP patch to `lblCode − 4` (inside the intro); if `8 ∤ size` the loop reads ⌊size/8⌋ qwords
  but the C model ⌈size/8⌉. The benchmark's `0x8200` is safe (`mod 2368 = 128`, `mod 8 = 0`).
* `TPCompCLoop` is exact only if the final pass's reads avoid the JMP-patched qword(s) (true unless
  `TPCompLoop` lies in the last ≤ 2368 bytes of `.text`).

**Data facts (Tables 4–6, RDTSCP unless noted).**
* 8,305,389 / 1,053,077 = 7.887 ("7.9×" ✓); 42,300,840 / 467,286 = 90.52 ("90.5×" ✓).
* Static SMC / dynamic SMC = 17.77; basic C / dynamic = 2.254 (minima 2.317). **No ratio ≈ 2.5** exists for
  "2.5× faster than the static SMC implementation".
* Estimator: 10,000·(467,286 − 414,188)/2,158,056 = 246.05 ✓, 2.46% ✓; non-SMC 3.635% ✓. The paper divides
  by **max**; a two-point model (each run takes min or max) gives (avg−min)/(max−min) = 3.045% (304.5 runs)
  for SMC and 7.784% for non-SMC.
* TSC ticks per 100 ns: 259.18, 259.12, 259.17, 259.19 → TSC ≈ 2.592 GHz (i7-9750H base 2.6 GHz).
* Static-SMC Multimedia minimum 1 ms although every run lasted ≥ 2.8806 ms (Interrupt Time min): not
  consistent with 1 ms quantization (observation O1, not an erratum).
* Clears: 83,198,361 / 10,000 = 8,319.84 per run = **1.99996 per qword for 0x8200/8 = 4,160 qwords**
  (0.295 per qword if the region were 220 KB). Loop variants: 449.3 and 459.8 per run ≈ 30 per pass
  (⌈4160/296⌉ = 15 passes). Cycles/qword: SMC 1,996; C 253; dynamic 112; C Loop 10,168.

---

## 2. Decisions (made; ask the user before deviating)

**D1 — Coverage standard: what "the whole paper is Lean-verified" means.** Every row of `PAPER_MAP.md`
has exactly one class:

| Class | Meaning | Discharged by |
|---|---|---|
| **F** | mathematical/algorithmic statement | Lean theorem, no platform hypotheses |
| **FC** | statement about timing/hardware/OS behaviour | Lean theorem whose hypotheses are fields of the platform contract (D2) or the paper's own assumptions A1–A4 |
| **FD** | number or ratio reported from measurements | Lean `decide` check on the transcribed tables (`Spec/Data.lean` is *not* Challenge surface) |
| **M** | the Lean model matches the artifact | mechanical evidence: MASM listing / AsmJit dump bytes = Lean encodings, native differential vectors |
| **R** | third-party platform fact (API, MSR number, latency table) | primary-source citation in `PAPER_MAP.md` |
| **X** | observation, opinion, design intent, future work | listed explicitly; nothing claimed |

Permitted public wording after R14: *"All mathematical, algorithmic and quantitative statements of
arXiv:2604.12407v1 are verified in Lean 4, unconditionally or relative to an explicitly stated platform
contract, with corrections listed in the errata; platform facts are cited and empirical observations are
listed as such."* Never shorten this to "the paper is proved" without the contract qualifier.

**D2 — Platform contract: black-box models, no white boxes.** Windows and the CPU are never modelled
internally. Each is replaced by an *interface contract* stated as Lean `structure`s whose fields are
hypotheses (never `axiom`s), so every dependence is visible in theorem statements and the axiom audit
stays clean. Theorems quantify over all parameter values satisfying the contract; R9/R10 then show the
paper's data are *consistent* with some parameter values (FD). Components:
1. **ISA (architectural) model** — a definition, not a hypothesis: the x86-64 subset of §R3, fetch from
   *current* memory bytes (same-thread SMC coherence, Intel SDM Vol. 3A "Handling Self- and
   Cross-Modifying Code"). Fidelity to silicon is M-class evidence (native vectors), never proof.
2. **Clear contract** `ClearRule g W κ`: a store triggers a machine clear iff one of the next `W` fetched
   instructions has a byte in the same `g`-byte granule as the store address (`g = 1` exact, `64` line,
   `4096` page); each clear costs `κ`. Base cost per instruction class is an unknown function.
3. **Timer contract**: a timer is a counter with resolution `r` and unknown phase φ; a reading of
   `[s, e)` is `⌊(e+φ)/r⌋ − ⌊(s+φ)/r⌋`.
4. **Scheduler/noise contract**: per run, at most `⌊L/q⌋ + 1` clock interrupts of cost ≤ `δ` and an
   adversarially placed number `p` of preemptions of cost ≤ `D`; "disturbed" = noise above `ν`. A window
   of `k` consecutive runs contains at most `r < k` disturbed runs (deterministic form); i.i.d. Bernoulli
   form is a *could* item.
5. **Adversary/assumption contract**: the paper's A1–A4 (§10) as a `structure Assumptions`, plus the
   attacker classes "code patcher", "split memory" (instruction fetch from a pristine copy, as in the
   Wurster–van Oorschot–Somayaji attack on self-checksumming), "faithful emulator", "external writer".
`lean/PLATFORM_CONTRACT.md` (written in R9, final in R14) lists every field: meaning, why plausible,
primary source, evidence, and what is *not* claimed.

**D3 — Two-level kernel model.** *Level 1* (`Spec/Kernel.lean`): an abstract SMC checksum machine
whose opcode state lives in the same byte memory that the checksum reads (introspection is exact),
including the termination patch bytes. *Level 2* (`Spec/ISA.lean`, `Spec/Images.lean`): the actual
x86-64 bytes of `TPComp` and `TPCompLoop`, proved to refine Level 1. The C models (`TPCompC`,
`TPCompCLoop`) are transcribed literally into `Spec/CModel.lean` (C expressions kept, incl. `preserve`
masks and the `adjustOffsets` map) and proved equal to Level 1. Static kernel: Level 2 is **must**.
Unrolled kernel: Level 1 **must**, Level 2 **should** (R7).

**D4 — Lean setup.** Pins as in selfspectre/smcTuring (accepted by Palomar): Lean
`leanprover/lean4:v4.35.0-rc3` (installed locally). **No Mathlib**: all planned content is
`BitVec`/`Nat`/`List` work and fits Lean core; this avoids the local memory problems selfspectre hit. If a
*could* item needs Mathlib, ask first, then `require` Mathlib at rev
`5e043698502894993991089b2dd893867c0db5c2` and build that module in CI only. Package `selfmodtamper`,
library `SmcTamper`, Palomar namespace `PalomarSMT`, `autoImplicit = false`. Headers in the smcTuring style
(`module` / `public import …` / `public section`) as in `../selfspectre/lean/WriteExecute/Spec/Speculation.lean`.

**D5 — Reuse infrastructure by copying, not Lean code.** From `../selfspectre` at commit `12160a3`
(`git -C ../selfspectre show 12160a3:<path>`), copy and adapt names/paths, keep behaviour, and record
source path + SHA-256 + edits in `lean/VENDORED.md`:
`validation/{limited_run,memory_budget,lean_build,build_modules,axiom_audit,make_challenge,audit_errata,make_errata,extract_layout,run_listings,native}.py`,
`validation/palomar/{fetch_policy_assets,refresh_policy,validate_metadata}.py`,
`.github/workflows/{proof,palomar-full}.yml`; as templates only: `lean/errata/{POLICY.md,edits.json,selfspectre-2019-errata.tex}`,
`lean/{formalization.yaml,comparator.json,PALOMAR_SEMANTICS.md,PALOMAR_SUBMISSION.md,LICENSE_AUDIT.md,PAPER_MAP.md}`.
Drop `prepare_mathlib.py` (D4). No Lean files are vendored: the selfspectre byte model has a different opcode set.

**D6 — Spec modules are the Challenge surface.** Every definition used in a selected statement lives in
`lean/SmcTamper/Spec/*.lean`: core imports only, `@[expose] def`, compact, no lemmas, docstrings that
claim nothing beyond the definition. `validation/make_challenge.py` generates `Challenge.lean` from them.
`Spec/Data.lean` (transcribed tables) is not selected.

**D7 — Tactic and axiom policy.** Forbidden: `sorry`/`admit` (outside Challenge), `axiom`,
`native_decide`, `bv_decide`, `Lean.ofReduceBool`, `implemented_by` in Spec, `unsafe`, `partial` in Spec.
`decide` is fine up to a few thousand cases over `Nat`/`Fin`/`BitVec 8`; split larger checks into
`List.all` chunks of ≤ ~4,000 cases (selfspectre R4 lesson). 64-bit facts with symbolic operands: `BitVec`
extensionality (`BitVec.eq_of_getLsbD_eq`) + `simp` + `omega`, never `decide`. `maxHeartbeats` above
400000 only with a one-line justification.

**D8 — Compute.** All builds/tests serially through `python validation/limited_run.py -- <cmd>`
(1.5 GB aggregate cap, Lean `-M768 -j1`). A capped failure is a failed check. No SSH/remote servers.
Cold full builds and the Palomar preflight run on GitHub Actions. Python: `PYTHONIOENCODING=utf-8`,
`open(..., encoding='utf-8')`; `pdftotext -enc UTF-8`.

**D9 — Errata list, tag, arXiv v2 (sequence of §0).**
* Errata are paper-only (§0). `edits.json` is the single source. Fields: `id`, `page`, `location`, `kind`
  (`replace|insert_after|clarify`), `before` (exact v1 TeX, also found in the v1 PDF text), `after`,
  `reason` (one sentence), `class` (`formal|mechanical|editorial`), `status`
  (`confirmed|ask-author|withdrawn`), `confidence` (`certain` or `inferred`, with the evidence in `evidence`),
  `lean_refs`, `evidence`, `source`. `make_errata.py` generates `ERRATA.md` and the errata TeX from it.
* The errata list is finished before the Palomar package (R13), because `formalization.yaml` names the
  corrections as fidelity divergences.
* `paper/arxiv-v1/` (pristine e-print + `SHA256SUMS`; committed, CC BY 4.0) is never edited.
* After the user reports the registration (R16): create an annotated tag on the registered commit (name
  confirmed with the user; suggested `palomar-v1`) and push it. Then `validation/apply_edits.py` builds the v2
  TeX from v1 + the `confirmed` items, plus one new paragraph or short "Formal verification" subsection (the
  author chooses where) and one bibliography entry for the formalization. `paper/v1-v2.diff` must contain
  exactly the edits plus that addition (`audit_errata.py` checks); `latexdiff` gives the visual differential.
* The v2 statement uses the D1 wording, names the platform contract, and says nothing beyond the
  registered statement. The v2 commit comes after the tag; the tag stays on the registered commit.

**D10 — Palomar selection and fidelity.** Select only result families of research interest:
`EmulationExact`, `SplitMemoryDetection`, `HarvardSeparation`, `ClearAvoidance`, `TamperEvidence`
(+ `EmulationStateBound` if proved). Elementary arithmetic (ratios, layout numbers, table checks) stays
supporting material (selfspectre review 1 rejected a separately selected index-arithmetic result). Every
sentence of `formalization.yaml`, `PALOMAR_SEMANTICS.md` and Spec docstrings must claim no more than the
Lean hypotheses give: observable claims need their freshness/initial-state hypotheses stated; contract
results must say "under the contract" (selfspectre lost three review rounds to this).

---

## 3. Target layout

```
CLAUDE.md                              standing rules (auto-loaded)
lean/
  FORMALIZATION_PLAN.md  ROUNDS.md     this plan; state machine + handoff notes
  lean-toolchain  lakefile.toml  lakefile.proof.toml (buildDir = ".lake/proof-build")
  SmcTamper.lean                       root import
  SmcTamper/Spec/{Bits,Kernel,CModel,ISA,Images,Contract,Detection,Harvard,Paper}.lean   Challenge surface (D6)
  SmcTamper/Spec/Data.lean             transcribed Tables 4–6 and Fig. 5 values (FD, not selected)
  SmcTamper/Bits/{Parity,Bytes,Mask,Opcode}.lean
  SmcTamper/X64/{Encode,Decode,Step,Run,Facts}.lean
  SmcTamper/Static/{Image,Iter,Loop,Emulation,ConstantFlow}.lean
  SmcTamper/Unrolled/{Layout,Level1,Emulation,StateBound,Image,Unit,Pass,Intro,Terminate,Restore,Refine}.lean
  SmcTamper/Layout/{Numbers,AsmJitSize,LayoutData}.lean
  SmcTamper/Harvard/{Machine,NonInterference,Interp,Separation,SplitMemory}.lean
  SmcTamper/Contract/{Clears,StaticClears,UnrolledClears,Timers,Noise,Estimator,Overhead}.lean
  SmcTamper/Detection/{Predicate,Collision,Policy,Reset,Assumptions,Negative}.lean
  SmcTamper/Data/{Ratios,Consistency}.lean
  SmcTamper/Paper.lean                 proofs of the Spec/Paper Props
  Challenge.lean Solution.lean comparator.json formalization.yaml           (R15)
  PAPER_MAP.md VENDORED.md PLATFORM_CONTRACT.md PALOMAR_SEMANTICS.md PALOMAR_SUBMISSION.md
  LICENSE_AUDIT.md FINAL_ACCEPTANCE.json
  errata/{POLICY.md, edits.json, ERRATA.md, smctamper-2026-errata.tex, QUESTIONS.md}   paper only
  CODE_FIXES.md                        code/docs fixes with commit hashes (not errata)
paper/
  arxiv-v1/{SelfModifyingCodeTamperProofingManuscriptUpdated.tex, biblio.bib, Tamperproof.eps, 00README.json, SHA256SUMS}
  SelfModifyingCodeTamperProofingManuscriptUpdated.tex  biblio.bib  Tamperproof.eps   (arXiv v2, R16)
  v1-v2.diff
validation/
  limited_run.py memory_budget.py lean_build.py build_modules.py axiom_audit.{py,lean}
  make_challenge.py audit_errata.py make_errata.py apply_edits.py coverage_audit.py
  extract_layout.py run_listings.py native.py Vectors.lean
  native/{smc_harness.cpp, CMakeLists.txt}   evidence harness (includes the product source, D-R12)
  layout/{tp_x64.json, dyn_x64.json}  data/paper_tables.json  reference/  rounds/R*.json  palomar/…
output/pdf/
.github/workflows/{proof.yml, palomar-full.yml}
```

Add `lean/.lake/`, `validation/.build/`, `validation/.cache/`, `output/pdf/*.aux`, `output/pdf/*.log`,
`__pycache__/`, `/.private/` to `.gitignore`.

---

## 4. Global rules

**Economy.**
1. One round per session; read only the current round. Build only touched modules
   (`lean_build.py SmcTamper.Static.Iter`); full build once at round close.
2. Modules ≤ ~300 lines. State the theorem first, then prove. Commit compiling increments.
3. A proof obstacle gets at most three focused attempts. Then weaken or split the statement with an
   explicit hypothesis, record it in `PAPER_MAP.md` as an open obligation, and move on. Scope changes go to the user.
4. Never unfold long runs. Prove one-step lemmas, `run_add`, and per-iteration/per-unit lemmas, then induct.
5. Evidence is minimal: one `validation/rounds/Rk.json` per round (commit, commands, pass/fail, peak memory).

**Process.**
* All build/test commands go through `limited_run.py` (D8).
* Commit at green increments and push at round close (authorised 2026-10-15, recorded in `CLAUDE.md`); end
  commit messages with the attribution line from the system prompt. Never force-push, never move tags.
* Round close: full build, `axiom_audit.py`, round gate, update `ROUNDS.md` (state + 5-line handoff:
  done / next / open obligations), `PAPER_MAP.md`, `edits.json` `lean_refs`, `validation/rounds/Rk.json`,
  update the "Current round" line in `CLAUDE.md`, commit.
* At most one `AskUserQuestion` call per round (≤ 4 questions), at the start, only for decisions. Overflow
  questions go to `lean/errata/QUESTIONS.md` for the next round's call.

**Errata policy** (copy to `lean/errata/POLICY.md` in R1). Preserve the published construction and make
the smallest local correction that states its intended, provable result. Quote arXiv v1 exactly (TeX
source, also found in the PDF text); never attribute extraction artifacts to the paper. Only the paper's
text, tables, figures and captions can carry errata; code and docs fixes go to `lean/CODE_FIXES.md`. An
item is `confirmed` only when it is certain (a Lean declaration, an arithmetic check of the paper's own
numbers, or a primary source) or inferred from strong evidence written into the item
(`confidence: inferred`); anything else stays `ask-author` and is not applied to v2 until answered.
Classes: `formal` (cites Lean declarations), `mechanical` (cites layout/native evidence), `editorial`
(primary source or unambiguous internal inconsistency). Every item is self-contained (§0). Evidence is never
called proof. Keep the errata PDF ≤ 3 pages (target 2).

---

## 5. Seed inventory (verify in R1; IDs are stable)

### Claims (seed for `PAPER_MAP.md`; class per D1, round that discharges it)

| ID | Location | Claim | Class | Round |
|---|---|---|---|---|
| C01 | §1 ¶1 | SMC on a deterministic machine can be simulated by non-SMC code (Harvard interpreter) | F | R8 |
| C02 | Abstract, §1 ¶2, ¶4 | Timing-faithful non-SMC reproduction must read the code bytes it emulates; costlier under the cost contract | F + FC | R8 |
| C03 | §1 Model, §9 ¶1 | `P(T,C)` true iff code unmodified (overclaim, P04); corrected: completeness + conditional soundness | FC | R11 |
| C04 | §1 Model | "constant-time kernels": control flow and instruction count are data-independent | F | R4, R6 |
| C05 | §1 Model | data stored as code (SMC-backed storage) is covered by the checksum | F | R11 |
| C06 | §1 "Relation to prior work", §10 A1 | SMC checksumming detects memory-splitting (Harvard-mimicking) attacks that defeat plain self-checksumming; hence A1 | F | R8 |
| C07 | §2 ¶1 | RDTSC/RDTSCP reliable statistically via repetition | FC | R10 |
| C08 | §2 ¶4–5 | coarse timers unsuitable for microbenchmarks (resolution) | FC | R10 |
| C09 | §2 ¶4 | Interrupt Time, QPC, precise UTC in the same precision class | FD | R10 |
| C10 | §2, §3 | API/toolchain facts (Windows/Linux clocks, MSVC inline asm, `/SECTION`, `VirtualAlloc`, `mmap`) | R | R1 |
| C11 | §3 ¶5 | dynamic generation makes the monitored addresses contextual | F | R6 |
| C12 | §4 ¶1, ¶3 | modifying in-flight code triggers machine clears; naive SMC is slow | FC | R9 |
| C13 | §4 ¶2 | unrolling + distinct pages reduce clears | FC | R9 |
| C14 | §4 ¶4 | detection granule → false positives | FC | R9 |
| C15 | Table 1 | MSR/event identifiers (Intel, AMD) | R + M | R1, R12 |
| C16 | §4 ¶6 | PMCs only for measurement, not needed by the mechanism | M | R5 |
| C17 | Table 2 | opcode pattern, bits 3–5, 2-bit toggle closure | F | R2 |
| C18 | Table 2 | LAT/RCP values | R (P07) | R1 |
| C19 | Table 3 | instruction and condition-code semantics (S, G, P) | F + R | R3 |
| C20 | Fig. 2 | encodings in comments, `$-2-3-3-3-2-3` targets the ADC opcode | F + M | R3, R5 |
| C21 | Fig. 3 | the C++ code emulates the SMC kernel precisely (with stated preconditions, P06) | F | R4 |
| C22 | §5 ¶5 | RIP-relative addressing reaches nearby code without an address register | F + R | R3 |
| C23 | §5 last ¶ | unrolling: emulator must track more sites as depth grows | F (should) | R6 |
| C24 | §5 last ¶ | with suitable offset and depth, clears may disappear | FC | R9 |
| C25 | Fig. 4 | snippet = 27-byte unit; `+1` skips the REX prefix | F + M | R3, R5 |
| C26 | §6 ¶2 | sizes measured with placeholders equal the emitted sizes | F + M | R5 |
| C27 | §6 ¶3 | dual-page layout: each unit writes the corresponding offset in the other page | F | R5, R6 |
| C28 | §6 ¶3 | branch-free termination by SMC; code restored afterwards | F | R6, R7 |
| C29 | Fig. 5 | 148 units/page, intro 0x5F, unit 0x1B, base + size = end | F + FD + M | R5 |
| C30 | §7 ¶1 | static SMC ≈ 7.9× slower | FD | R10 |
| C31 | §7 ¶1–2 | heavy tail; minima stable; calibrate from quantiles | FC + X | R10, R11 |
| C32 | §7 ¶3 | dynamic ≈ 90.5× faster than non-SMC | FD | R10 |
| C33 | §7 ¶3 | ≈ 2.5× faster than static SMC (inconsistent, P02) | FD | R10 |
| C34 | §7 ¶3 | 3–4 pages no material improvement | X (data not reported) | R1 |
| C35 | §7 ¶4 | 246 runs / 2.5% / 3.6% estimate (P01) | FD + FC | R10 |
| C36 | §7 ¶5, Table 6 | naive SMC clears ≫; unrolled reduced; clears at the start of unrolled iterations | FD + FC | R9 |
| C37 | Tables 4–5 | cross-timer consistency (TSC ≈ 2.59 GHz) | FD | R10 |
| C38 | Tables 4–5 | measured interval contents (P05) | M | R12 |
| C39 | §8 ¶1 | `c_nonSMC O(n) ≫ c_SMC O(n)` (notation, P09) | FD + X | R10 |
| C40 | §8 ¶2 | optimality hard, combinatorial; compilers can beat hand asm | X | R1 |
| C41 | §8 ¶3 | Pentium III remark; branching expensive | X | R1 |
| C42 | §8 ¶3 | design rule: never modify the currently executing page | FC | R9 |
| C43 | §8 ¶3 | task switches dominate perturbation; priority mitigates | FC + X | R10 |
| C44 | §9 ¶1 | many units; validation state machine; reset bounds state growth | F | R11 |
| C45 | §9 ¶2 | thresholds from quantiles; k consecutive failures | FC | R11 |
| C46 | §10 | A1–A4 scope the model; each is necessary (counterexamples) | F | R11 |
| C47 | §10 ¶2 | reconfigurable hardware compatible; not attestation | X | R1 |
| C48 | §11 | summary restates C12–C45 | (refs) | R14 |

### Paper errata seeds (P)

Status per the author's instruction "if you are sure those are errata, fix them" (2026-10-15):
**confirmed** = include in the list and in v2; **inferred** = include, with the evidence written into the item;
**ask-author** = list in `QUESTIONS.md`, apply only after an answer. R1 re-verifies every excerpt and number
before anything is written to `edits.json`.

| ID | Location (v1) | Published text → correction | Class | Status |
|---|---|---|---|---|
| P01 | §7 ¶4 display and next sentence | The estimate divides by `max`. Under its own model (a run is undisturbed, taking `min`, or disturbed, taking `max`) the disturbed fraction is (avg − min)/(max − min): ≈ 304 runs = 3.0% for SMC and 7.8% for non-SMC (not 246 / 2.5% / 3.6%). Keep "back-of-the-envelope"; optionally add the rigorous "at least 304 runs exceeded the minimum" | formal (FD) | confirmed |
| P02 | §7 ¶3 | "about 2.5× faster than the static SMC implementation" → "about 17.8× faster than the basic static SMC implementation" (Table 4 vs Table 5: 8,305,389 / 467,286); no ratio in the tables equals 2.5 | formal (FD) | confirmed |
| P03 | Table 4 caption | "the entire 220 KB code segment" → "the entire 32.5 KiB (0x8200-byte) code segment". Evidence: Fig. 5 prints `size: 0x8200`; Table 6 gives 83,198,361 / 10,000 = 8,319.84 clears per run = 2.0000 per qword for 4,160 qwords, and the naive kernel must clear at least once per qword (220 KB would give 0.295) | editorial + mechanical | inferred |
| P04 | §1 "Model"; §9 ¶1 | "returns true if and only if the protected code remains unmodified" → returns true for unmodified code (within the timing contract) and false for every modification that changes the checksum state or exceeds the time threshold; checksum collisions exist (Lean witness), so "if and only if" cannot hold | formal | confirmed |
| P05 | Tables 5–6, §7 | Provenance: in the repo code the labels "SMC Loop"/"Dyn SMC Loop" are swapped relative to the functions, so the two Table 6 rows (and possibly the source block of Table 5) may be swapped; each timed interval also contained a console write and a counter read (ratios then conservative). Erratum only if the 2022 measurement code equalled the repo code | mechanical | ask-author |
| P06 | Fig. 3 caption | "The three arguments are the start address `pData`, the protected length `ulSize`, and the function start address `pTPCompOffset`" → the arguments are `pData`, `ulSize` and `pResult`; `pTPCompOffset` is the address of `TPComp`'s body. "Precisely" holds for an 8-byte-aligned region with synchronised opcode state (Lean preconditions) | formal + editorial | confirmed |
| P07 | Table 2 LAT/RCP | Check every value against the cited AsmGrid and uops.info for the `r64, m64` forms; a CMP *latency* of "0.2 / 0.25" cycles is implausible | editorial | ask-author until R1 checks the source; confirmed if the source contradicts the table |
| P08 | §1 "Model" | "constant-time algorithmic kernels" → kernels whose control flow and instruction count do not depend on the data (per-operation costs still differ, Table 2) | formal | confirmed (clarification) |
| P09 | §8 ¶1 | `c_nonSMC O(n) ≫ c_SMC O(n)` → `c_nonSMC·n ≫ c_SMC·n` (measured ≈ 10,168 vs 112 cycles per qword); "must generally spend more space-time resource" is Assumption 3, not a theorem | formal + editorial | confirmed (clarification) |
| P10 | Table 3 | "SHL Shift left (unsigned)" → "logical shift left (same as SAL)" | editorial | optional; drop if the list gets long |

### Code (L) and docs (D) seeds — not errata (§0); tracked in `lean/CODE_FIXES.md`; all land before the Palomar commit

| ID | File | Fix (minimal) | Test |
|---|---|---|---|
| L01 | `.cpp` 684 | swap the last two `strFuncNames` | harness label check |
| L02 | `.cpp` 697–703 | move the per-run `std::cout`/IOCTL after `endTimer` | native run (timing only) |
| L03 | `.cpp` 421, 458 | follow the thunk only if `*(PBYTE)TPComp == 0xE9` | Release differential vectors |
| L04 | `TP.asm`, `gen_asm`, `.cpp` | document/assert loop precondition `size ≥ 8 ∧ 8 | size` | edge vectors |
| L05 | `gen_asm` | assert emitted intro size == measured `introbytes` (only if R5 confirms the cancellation) | harness dump |
| L06 | `TP.asm` 5 | note that `TPCompLoop` is not page-aligned (or enable the segment) — author choice | listing |
| D01 | `README.md` | "not yet available on arXiv" → arXiv:2604.12407; Lean section (R15; Palomar ID and tag added in R16) | — |
| D02 | `CITATION.cff` | preferred citation → arXiv preprint | `cffconvert` optional |
| D03 | `README.md` variant table | consistent with L01 | — |

---

## Rounds

Sizing: one session each unless noted. Priority: **must** / should / could. If budget runs short, the
**must** items alone still give a Palomar-ready, fully classified result ("MVP path").

### R0 — Bootstrap, references, baselines (must)

1. No question this round: the decisions are recorded in `CLAUDE.md` (2026-10-15): commit and push
   authorised; the arXiv source and PDF may be committed (do so, D9); the dissertation is out of scope;
   never write to OneDrive.
2. `paper/arxiv-v1/`: download the e-print tarball into a fresh directory, extract, verify the four
   SHA-256 values of §0, write `SHA256SUMS`. Copy to `paper/` (the future v2). Build both with
   `latexmk -pdf` (the arXiv `00README.json` says `latex`; `Tamperproof.eps` needs `epstopdf`, which MiKTeX
   provides) into `output/pdf/`; record page counts.
3. `validation/reference/`: `2604.12407v1.pdf` (verify SHA-256) and `2604.12407v1.txt`
   (`pdftotext -layout -enc UTF-8`).
4. Lake project (D4): `lean-toolchain`, `lakefile.toml` (package `selfmodtamper`,
   `defaultTargets = ["SmcTamper"]`, libs `SmcTamper`, later `Challenge`, `Solution`), `lakefile.proof.toml`.
   Root `SmcTamper.lean` importing a stub `SmcTamper/Spec/Bits.lean`.
5. Copy infra (D5) and write `lean/VENDORED.md`. Check `limited_run.py` on a trivial command. Build the stub
   with `lake build` under the guard; if Lake exceeds the cap, use `build_modules.py` (selfspectre R0 note).
6. `validation/axiom_audit.{lean,py}` adapted to prefixes `SmcTamper`, `PalomarSMT`. Passes on the stub.
7. `validation/data/paper_tables.json`: Tables 4–6 and the Fig. 5 values transcribed from the v1 TeX with
   TeX line numbers; a checker re-reads the TeX rows and compares (prevents transcription errors).
8. Native baseline: `validation/native.py` builds `SelfModTamper.sln` Debug|x64 and Release|x64 (locate MSBuild
   via `vswhere`; `--toolset v143` override for CI). The product needs admin + WinRing0 to *run*: do not run it;
   compile-only here. ml64 is found via `vswhere` (`VC/Tools/MSVC/*/bin/Hostx64/x64/ml64.exe`).
9. Create `lean/ROUNDS.md` entries, `.gitignore` additions (§3), `validation/rounds/R0.json`.

**Gate:** v1 hashes verified; both TeX copies build; stub builds and audits clean under the guard;
Debug/Release compile; tables JSON checker passes.

### R1 — Claim inventory, errata verification, author questions (must; text work)

1. For each P item: find the exact excerpt in the v1 TeX and confirm it in the PDF text (page number);
   recompute every number it uses. Then scan the whole paper once for further
   *mathematical/quantitative/algorithmic* errors (no typo hunting); add new P items with a status per §4.
2. Verify every R-class claim (C10, C15, C18) against primary sources: Microsoft Learn pages for the APIs,
   Linux man pages, Intel SDM (MSR 0x38F/0x186/0xC1; event C3H umask 04H MACHINE_CLEARS.SMC; CR4.PCE),
   AMD PPR/BKDG (MSRs C000_0301, C001_0000, C001_0004; PMCx021), uops.info and AsmGrid for Table 2. Record
   URL + section in `PAPER_MAP.md`. A value that disagrees becomes a P item (this settles P07).
3. Write `lean/errata/POLICY.md` (§4), `edits.json` (D9 schema; P items only; `lean_refs` filled as the
   rounds prove them), `lean/CODE_FIXES.md` (L, D items), `lean/PAPER_MAP.md` (C01–C48 + new; columns:
   ID, v1 location, claim, class, round, status, declaration/evidence).
4. `validation/audit_errata.py --inventory`: every `before` occurs verbatim in the v1 TeX and, after
   normalising whitespace/hyphenation/ligatures/TeX markup, in the PDF text.
5. Last step, one `AskUserQuestion` (≤ 4) only for items still `ask-author`: P05 (was the 2022 measurement
   code the repo code — labels and the print inside the timed interval?), P07 if the source leaves a choice,
   L06 (page-align `TPCompLoop` or only document it), and whether v2 should disclose the timed-interval
   contents. Record answers in `edits.json`/`CODE_FIXES.md`.

**Gate:** inventory audit passes; every claim has a class; every P/L/D item has a class, a status and planned evidence.

### R2 — Bits, parity, opcode family, masks (must)

`Spec/Bits.lean` (`@[expose]`): `Mem := Nat → BitVec 8`; `rd64 m a` (little-endian, `m a` least
significant); `wr8`; `evenParity8 (b : BitVec 8) : Bool`; `pf (x : BitVec 64) := evenParity8 (x.setWidth 8)`;
`sf (x : BitVec 64) := x.msb`; `opOf (b : BitVec 8) : Nat` (bit 3 → 1, bit 5 → 4); `opcodeOf (op : Nat) : BitVec 8 := 0x13 ^^^ (op <<< 3)`;
`toggle (res : BitVec 64) : Nat := (if pf res then 4 else 0) ||| (if sf res then 1 else 0)`;
`aluField (b : BitVec 8) : Nat := (b.toNat >>> 3) % 8`; `paritybyteC (v : Nat) : Bool` = the C `0x6996` expression.

Proofs (`Bits/*.lean`):
* `Opcode`: Table 2 opcode/field pairs for all eight ops (`decide`); `{0x13,0x1B,0x33,0x3B}` closed under XOR
  with `toggle … <<< 3` and contains exactly ADC/SBB/XOR/CMP; `opOf (opcodeOf op) = op` and
  `aluField (opcodeOf op) = op ^^^ 2` for `op ∈ {0,1,4,5}`; the mask touches bits 3 and 5 only (two bits).
* `Parity`: `paritybyteC v = !evenParity8 v` for all `v < 256` (256-case `decide`).
* `Mask` (the key lemma for Fig. 3): for `j < 8`, op ∈ {0,1,4,5}, any `x : BitVec 64` whose byte `j` is one of
  the four opcodes, `(x &&& ~~~(5 <<< (8*j+3))) ||| (op <<< (8*j+3)) = x` with byte `j` replaced by `opcodeOf op`.
  Strategy: fix `j` and `op` (32 instances via a small generic lemma), `BitVec` ext, `simp`, case on bit index.
  Fallback: state it via `rd64 (wr8 m a b) (a/8*8)`.
* `Bytes`: `rd64_wr8_outside`, `rd64_wr8_inside` (byte position `a % 8` when `8 | base`), `wr8` frame lemmas.

**Gate:** all of C17 proved; mask lemma proved (or narrowed with a recorded obligation).

### R3 — x86-64 subset model (must) — R3a encodings/decoding, R3b semantics (two sessions)

`Spec/ISA.lean`. Registers `Fin 16` (RAX=0, RCX=1, RDX=2, RBX=3, RSP=4, RBP=5, RSI=6, RDI=7, R8=8); 8-bit
low registers AL/CL/DL/BL only (codes 0–3 need no REX). Flags `CF PF ZF SF OF` (AF not modelled: no
instruction here reads it — state this in the docstring). State: `regs : Fin 16 → BitVec 64`, `rip : Nat`,
flags, `mem : Mem`. Addresses are `Nat`; theorems assume the involved addresses < 2^63.

Forms (exactly those in `TPComp`, `TPCompLoop`, the generated code; extend only if a listing shows another):
`aluRM` (`REX.W op /r`, mod=00, op ∈ 03/0B/13/1B/23/2B/33/3B — generic over the 3-bit field so the patched
opcode decodes uniformly), `setcc r8` (`0F 98`, `0F 9A`), `shl r8, imm8` (`C0 /4`), `or r8, r8` (`08`, `0A`),
`xor m8[rip+d32], r8` (`30 /r`), `lea r64,[b+i]`, `lea r64,[b+d8]`, `mov r64,r64` (`89`, `8B`), `xor r64,r64`
(`31`, `33`), `cmp r64,r64` (`39`, `3B`), `sub r64,r64`, `clc`, `jcc rel8` (G, L), `jmp rel8/rel32`,
`add/sub/cmp r64, imm8/imm32` (`83`, `81`), `add r32, imm8/imm32`, `shr/shl r64, imm8` (`C1 /5`, `/4`),
`dec r64` (`FF /1`), `imul r64, r64, imm8` (`6B`), `mov r64, simm32` (`C7 /0`), `mov r32, imm32` (`B8+r`),
`mov r64, imm64` (`REX.W B8+r`), `add/sub m32[rip+d32], r32` (`01`, `29`), `xor m64[rip+d32], r64`
(`REX.W 31`), `mov [r64], r64` (`REX.W(B) 89`), `nop`. `push/pop/ret` are **not** modelled: theorems start
after the prologue and end at the result store (documented boundary).

* R3a: `encode : Instr → List (BitVec 8)`, `decode : Mem → Nat → Option (Instr × Nat)` (reads only the
  instruction's bytes, from **current** memory), round-trip for every constructor instance used.
  Prove C20 (Fig. 2 comment bytes; `$-16` lands on the ADC opcode) and C25 (unit = 27 bytes; the `+1`
  displacement hits the opcode byte) by `decide` on concrete encodings.
* R3b: `step`, `run n`, `run_add`, flag semantics per SDM (ADD/ADC/SUB/SBB/CMP: CF, OF, SF, ZF, PF; logic ops
  clear CF and OF; SHL count semantics; SETcc; `G` = `¬ZF ∧ SF = OF`), RIP-relative effective address =
  next `rip` + sext(disp32) (C22), C19 condition-code facts, the signed/unsigned compare lemma
  (`a, b < 2^63 → (JG taken after CMP a,b ↔ b < a) ∧ CF = 0`).

**Gate:** every used encoding round-trips; C19, C20, C22, C25 proved; one-step lemmas for each form.

### R4 — Static kernel: Fig. 2 ≡ Fig. 3 (must)

`Spec/Kernel.lean` (Level 1, static): `staticStep (opAddr) : KState → KState` reads the opcode byte at
`opAddr` from `mem`, reads `d := rd64 mem ptr`, computes the ALU result (`ADC`/`SBB` with CF = 0), writes
`mem opAddr ^^^ (toggle res <<< 3)`, advances `ptr` by 8; `staticRun` = ⌈size/8⌉ steps.
`Spec/CModel.lean`: literal `tpCompC` (fuel = ⌈ulSize/8⌉; `pModOffset`, `pModByteOffset`, `preserve`,
`switch (op)` incl. `default: res = 0`; returns `(sum, op)`). `Spec/Images.lean`: `tpCompImage base op :
Nat → Option (BitVec 8)` (the 14 prologue-free bytes from `MOV RSI,RCX` to `MOV [R8],RBX`, opcode byte
at `base + 0xF`).

1. `Static/Emulation` (L1 ≡ C): for 8-aligned `pData`, any `opAddr` (inside or outside the region), op
   byte ∈ the four opcodes: `staticRun` and `tpCompC` agree on `sum`, final op, and the region reads.
   Invariant: after k steps `mem = wr8 mem₀ opAddr (opcodeOf op_k)`; use the R2 mask lemma for the qword
   containing `opAddr`. Also `default` unreachable (C21).
2. `Static/Iter` + `Static/Loop` (L2 ≡ L1): memory agrees with `tpCompImage` (code bytes) and the region
   lies below 2^63 and does not overlap the stack/result; one iteration = 10 instructions refines one
   `staticStep` (case split on the 4 opcodes); CF = 0 at each ADC/SBB; loop count ⌈size/8⌉ by `JG`.
3. `Static/ConstantFlow` (C04, P08): the sequence of executed instruction addresses depends only on
   `pData`, `ulSize` (not on memory contents).
4. Theorem `static_emulation`: running the image from `MOV RSI,RCX` to `MOV [R8],RBX` stores `tpCompC`'s
   sum and leaves the image unchanged except the opcode byte = `opcodeOf` (C's final `op`). Hypotheses
   listed in the docstring (alignment, address bounds, non-overlap, function address resolved = P06/L03).

**Gate:** `static_emulation` proved with the hypotheses above; C04, C21 recorded.

### R5 — Layout numbers, assembled bytes, generated bytes (must)

1. `Layout/Numbers` (`decide`): §1 layout facts — 148, 4091 + 5 NOPs, `rsi(k)`, opcode offsets `0x60` and
   `4097 + 27i`, distinct qwords for all 296 opcode bytes, 7974, mask `0x4808498DA1`, patch target 8097 for
   all k < 296, Fig. 5 address sum, `0x8200 mod 2368 = 128`.
2. `validation/run_listings.py` + `extract_layout.py`: `ml64 /c /Fl /Sa TP.asm` → listing + COFF →
   `validation/layout/tp_x64.json` (label offsets, bytes of `TPComp` and `TPCompLoop`, NOP pad, `jmp L0` form).
3. Generated bytes: `validation/native/smc_harness.cpp` (R12 also uses it) does
   `#define main smt_product_main` then `#include "../../SelfModTamper/SelfModTamper.cpp"`, links `TP.asm` and
   AsmJit (vcpkg), and in `--dump-dyn <file>` mode calls `gen_asm` in a temp directory and writes the code
   bytes → `validation/layout/dyn_x64.json`. No product source change.
4. `Layout/LayoutData.lean` generated (deterministic script) from both JSON files; `decide` checks that the
   bytes equal the R3 encodings of the R4/R6 images (C20, C25, C27, C29). Settles §1 "placeholder
   measurement": `Layout/AsmJitSize` proves the intro length for both parameter sets under the encoder
   choices observed in the dump; if the cancellation is real, keep L05, else drop it.
5. C16: byte scan that the kernels contain no `RDPMC`/`RDMSR`/`WRMSR`/`CPUID` (M).

**Gate:** listing and dump bytes equal the Lean encodings (0 mismatches); C29 proved; L05 decided.

### R6 — Unrolled kernel, Level 1 (must)

`Spec/Kernel.lean` (unrolled part): unit opcode address `uop u = start + offset u + 1` (from `Layout`),
`unitStep u` = `staticStep`-like but writes `uop ((u + 148) % 296)`; a pass runs units `0..295`; the final
pass with `n ∈ [1,296]` units first XORs the patch bytes at unit `n−1` offset 23, runs units `0..n−1`, then
XORs them back. `Spec/CModel.lean`: literal `tpCompCLoop` (`lc`, `op[296]`, `adjustOffsets` as a function
from qword address to `(byteidx, idx)`, `preserve[8]`).

1. `Unrolled/Level1` + `Unrolled/Emulation`: for `size ≥ 8`, `8 | size`, 8-aligned region, and the
   hypothesis "the final pass reads no qword overlapping the patch bytes": L1 ≡ `tpCompCLoop` (sum, op
   array) and the image after the call equals the image before except opcode bytes (C28, restoration).
2. Counterexamples (formal, for L04): `size mod 2368 ∈ [1,7]` → the patch index is −1 (`lblCode − 4`);
   `8 ∤ size` → L1 reads ⌊size/8⌋ qwords while `tpCompCLoop` reads ⌈size/8⌉.
3. C11: the opcode-address set is `start + const`; for every finite address set there is a `start` whose
   opcode addresses leave it.
4. C04 for the unrolled kernel: the executed unit sequence depends only on `size`.
5. *(should)* `Unrolled/StateBound` (C23, Myhill–Nerode): for depth `d` sites, all `4^d` opcode configurations
   are reachable from canonical within one pass and pairwise distinguishable by some continuation; hence any
   deterministic emulator with a state function has ≥ `4^d` states (≥ 2d bits). Prove for generic `d`
   over the Level-1 machine.

**Gate:** L1 emulation + restoration proved; counterexamples proved; C11 recorded.

### R7 — Unrolled kernel, Level 2 (should) — up to two sessions

`Spec/Images.lean`: `loopImage base ops` (intro 95 B, 296 units, NOP pad, `jmp L0`, epilogue, from the R5
layout data). Prove: unit lemma (8 instructions refine `unitStep`), page-transition lemma, full pass by
induction over units (never unfold 296 units), intro full/partial paths including the self-modified
displacement (`add [L4−4],esi` changes the next instruction's `disp32`; prove the effective address equals
unit `n−1` + 23), JMP to 8097, epilogue restoration, and `unrolled_refines`: Level 2 ⇒ Level 1. Bound
addresses (< 2^63) as hypotheses.

**Gate:** `unrolled_refines` proved, or the remaining lemma recorded as an open obligation with Level 1 + R5
byte equality as the fallback claim.

### R8 — Von Neumann vs Harvard, split memory (must)

`Spec/Harvard.lean`: a *Harvard machine* has a fixed control (type `C`), registers and a data memory; each
step reads one data address determined by control + registers, then updates control/registers and
optionally writes one data byte. A *von Neumann machine* fetches its instruction from the same memory it
writes (generic over a decode function reading ≤ `L` bytes).

1. `Harvard/NonInterference`: Harvard runs from memories agreeing on every address the run reads are equal
   (induction; the read list is computed on either memory).
2. `Harvard/Interp` (C01): for every vN machine there is a Harvard machine (the interpreter: `L` fetch reads,
   one dispatch, execute) simulating it step for step with ≤ `L + w + 1` Harvard steps per vN step.
3. `Harvard/Separation` (C02): if a Harvard machine simulates a vN machine on all memories (same observation)
   then for every memory and every *sensitive* fetched byte (changing it changes the vN observation) the
   Harvard run reads that byte. Corollary under the cost contract (each Harvard data read costs ≥ ρ beyond
   native execution): Harvard time ≥ vN time + ρ·(number of sensitive fetched bytes).
4. `Harvard/SplitMemory` (C06): Level-1 kernel under split memory (fetch from a pristine copy, data reads and
   the SMC writes go to the other copy) computes a different checksum from the vN run whenever some toggle in
   the run is non-zero (the opcode change takes effect only under vN); give an explicit small region where it
   differs (`decide`). Also: under split memory a *non*-SMC checksum is blind to code patches (the attack the
   paper's A1 excludes).

**Gate:** C01, C02, C06 proved.

### R9 — Clear contract (must)

`Spec/Contract.lean`: `Ev` (pc, len, cost class, optional store address), `ClearRule g W`, `clears`,
`Cost` (`base`, `κ`), `time`; trace extraction from Level 2 runs (static) and from Level 1 unit traces with
layout offsets (unrolled).

1. `Contract/StaticClears` (C12): for `W ≥ 4` and any `g ≥ 1`, the naive kernel has ≥ `n − 1` clears for `n`
   iterations; time ≥ `(n−1)·κ`.
2. `Contract/UnrolledClears` (C13, C24): with `g = 1`, unit stores cause no clears whenever `W` is below
   the minimum store-to-refetch distance (about 8·148 instructions; compute the exact value from the layout,
   including the `jmp L0` + intro path between passes); with `g = 4096` and a page-aligned image, unit-store
   clears per full pass ≤ `2·⌈W/8⌉`
   (only the two page transitions), plus ≤ 3 for the patch/displacement stores per call (C36 "clears at the
   start of unrolled iterations").
3. C14: for `g > 1` there is a trace where a store to a byte of no in-flight instruction causes a clear.
4. C42: if no store shares a granule with any of the next `W` instructions, `clears = 0`.
5. FD fit (`Data/Consistency`): the Table 6 data are consistent with the contract: static 1.99996 clears per qword
   (needs ≥ 1 per iteration ✓) and ≈ 30 per pass for both loops; exhibit `W` values in range.
6. Start `lean/PLATFORM_CONTRACT.md` (D2 items 1–2).

**Gate:** C12–C14, C24, C42 proved; fit recorded as FD.

### R10 — Timers, noise, estimator, data checks (must)

1. `Contract/Timers` (C08): reading bounds `⌊d/r⌋ ≤ reading ≤ ⌊d/r⌋ + 1`; indistinguishability: if
   `d₁ < d₂ < d₁ + r` some phase gives equal readings; observation O1 (Multimedia min 1 ms vs ≥ 2.8806 ms
   runs) violates resolution 1 ms — record as FD observation, not an erratum.
2. `Contract/Noise` (C07, C43): interrupt count monotone in run length; minimum of `k` samples ≤ every
   sample (minima as stable baseline); repetition lemma: if at most `r` of any `k` consecutive runs are
   disturbed and `k > r`, some run in each window is undisturbed.
3. `Contract/Estimator` (C35, P01): integer statistics as computed by the driver (`avg = Σ / N` floor,
   min, max); two-point identity; Markov count bound; lower bound `#{x > min} ≥ Σ(x−min)/(max−min)`; the
   paper's expression equals Markov with θ = max (vacuous as a bound). Plug in Table 5 (`decide`).
4. `Contract/Overhead` (P05): `a > b > 0`, `o ≥ 0` ⇒ `(a+o)/(b+o) ≤ a/b` (cross-multiplied), so ratios
   measured with a common additive overhead are conservative.
5. `Data/Ratios`, `Data/Consistency` (FD): 7.9 (C30), 90.5 (C32), the P02 ratios (C33), cross-timer
   consistency 259.1–259.2 (C37, C09), Fig. 5 values (C29), P03 clears-per-qword, efficiency constants
   (C39). All as `Nat` cross-multiplied inequalities, `decide`.
6. `PLATFORM_CONTRACT.md` D2 items 3–4.

**Gate:** all FD rows of `PAPER_MAP.md` checked; P01/P02/P03 numbers backed by declarations.

### R11 — Detection predicate, policy, assumptions (must)

`Spec/Detection.lean`: checksum units (region, kernel, canonical opcode state, expected value), the
predicate `P` (value match ∧ time ≤ τ), reset to canonical, alarm after `k` consecutive failures,
`Assumptions` (A1 von Neumann fetch, A2 some unneutralised unit covers each protected byte, A3 every faithful
non-SMC implementation exceeds τ, A4 no external writer between check and use).

1. `Detection/Predicate` (C03 corrected): completeness (unmodified + contract noise bound ⇒ `P`);
   soundness for value-changing modifications; timing soundness for any attacker slower than τ.
2. `Detection/Collision` (P04): an explicit pair of distinct images with equal checksum and final state
   (find with a script, prove by `decide`/`rfl`): the "iff" is false.
3. `Detection/Policy` (C45): deterministic noise contract ⇒ no false alarm with `k > r`; persistent
   slowdown ⇒ alarm within `k` runs; threshold from calibration samples (max/quantile) ⇒ no calibration-run
   alarm. *(could)* i.i.d. Bernoulli form `P(k failures) = p^k` over finite weights.
4. `Detection/Reset` (C44): with reset, the final opcode state is a function of the region contents, so one
   expected value per region suffices; without reset, the state after `j` calls depends on `j`.
5. `Detection/Assumptions` + `Negative` (C46, C05): main `tamper_evident` theorem under A1–A4 + contract;
   necessity witnesses: Harvard/split memory without SMC (R8) defeats A1-less schemes, all units neutralised ⇒
   no detection (A2), a faithful emulator under τ breaks timing detection (A3 is needed), an external writer
   can restore bytes before the check (A4). Data-as-code covered (C05).

**Gate:** C03, C05, C44–C46 proved; P04 backed.

### R12 — Code corrections and native acceptance (must)

1. Apply L01–L06 as decided (R1/R5) and D01–D03, minimal diffs, no refactors; record each in
   `lean/CODE_FIXES.md` with its commit hash. These are not errata (§0); all must land before the Palomar
   commit (R15), because the R16 tag freezes the code that the v2 manuscript points to.
2. `validation/native/smc_harness.cpp` modes: `--vectors` (no driver, no admin): (a) region = random buffers,
   (b) region = the harness `.text` (introspective). Runs `TPComp`/`TPCompC` and `TPCompLoop`/`TPCompCLoop`
   alternately in lockstep and the dynamic kernel against Lean-generated expected values
   (`lake env lean --run validation/Vectors.lean` → `validation/native/vectors.json`).
3. `native.py --all`: build Debug|x64 and Release|x64 of the product and the harness; run vectors. Expected:
   Debug passes; Release **fails before L03 and passes after** (record both). Edge vectors for L04.
4. `validation/rounds/R12.json`.

**Gate:** vectors pass in both configurations after the fixes; L items have commit hashes.

### R13 — Errata list (must; no manuscript changes yet)

1. Open `QUESTIONS.md` items → one `AskUserQuestion` if any are still open.
2. `validation/make_errata.py` → `lean/errata/ERRATA.md` and `lean/errata/smctamper-2026-errata.tex`
   (selfspectre template; title "Errata and model clarifications — Tamper-Proofing with Self-Modifying
   Code"; cites arXiv:2604.12407v1; per item: ID, location, exact before/after, one-sentence reason,
   confidence/evidence, Lean reference or source). No code section (code fixes are not errata). PDF in
   `output/pdf/`, ≤ 3 pages. Each item must be understandable without this repo (§0).
3. `audit_errata.py`: inventory, every `lean_refs` name exists (generated `#check` file
   `lean/ErrataRefs.lean` builds), PDF page count, no `confirmed` item without a Lean ref, number check or
   source.
4. Ask the author to review the errata PDF (the only question this round).

**Gate:** errata audit passes; PDF builds; author review requested.

### R14 — Coverage and fidelity audit (must)

1. `validation/coverage_audit.py`: every `PAPER_MAP.md` row has a class, status `proved`/`checked`/`cited`/
   `listed` and a declaration (F/FC/FD), evidence path (M), URL (R) or note (X); every declaration exists
   (generated `#check` file); every P item maps to a claim row; no row `todo`.
2. Fidelity pass (D10): reread every Spec docstring, `PLATFORM_CONTRACT.md`, and the planned README section
   against the Lean statements; fix overclaims. Finalise `PLATFORM_CONTRACT.md`.

**Gate:** coverage audit passes; the D1 wording is justified row by row.

### R15 — Palomar package, CI, handoff (must)

1. `Spec/Paper.lean`: Props `EmulationExact` (static Level 2 + unrolled Level 1, Level 2 if R7 done),
   `SplitMemoryDetection`, `HarvardSeparation`, `ClearAvoidance`, `TamperEvidence`, `EmulationStateBound`
   (if proved); `Paper.lean` proves each.
2. `make_challenge.py` → `Challenge.lean` (`PalomarSMT.mathematical_result : … ∧ …` with `sorry`);
   `Solution.lean`; `comparator.json` (standard three axioms, `enable_nanoda: true`). Limits: hard 1,000 lines /
   100 KiB, preferred 300 / 32 KiB (disclose if over).
3. `formalization.yaml` (schema v0.4, structure of `../selfspectre/lean/formalization.yaml`): MIT; sources:
   arXiv:2604.12407 (`adapts`, author participated), Intel SDM (background), Giffin et al. ACSAC'05 and
   Wurster et al. S&P'05 (background), selfspectre/smcTuring entries only if something is used; honest
   `status.scope` naming the platform contract; automation: Claude Opus 5.5 (planning), Claude Sonnet 5.5
   (execution), Claude Code. Validate with `validate_metadata.py` after `refresh_policy.py`.
4. `PALOMAR_SEMANTICS.md`, `LICENSE_AUDIT.md`, README "Lean formalization" section (D1 wording),
   `PALOMAR_SUBMISSION.md` (form values; `request_id: smctamper01`, `project_path: lean`).
5. CI: `proof.yml` (Linux cold build, axiom audit, `make_challenge.py --check`, `audit_errata.py`,
   `coverage_audit.py`; Windows job `native.py --all` with `--toolset v143`) and `palomar-full.yml`.
6. Push (authorised) and get `proof.yml` green. Dispatching `palomar-full.yml` needs the user's go-ahead:
   make it this round's single question. Record run URLs in `FINAL_ACCEPTANCE.json`. Hand the exact commit
   and the preflight run ID to the user for submission. The `formalization.yaml` source note names the
   corrections by errata ID (`errata/ERRATA.md`) as fidelity divergences.

**Gate:** cold CI green, preflight passing on the recorded commit, errata reviewed, coverage audit green,
commit handed over. Then wait for the user to report the registration (entry ID and version).

### R16 — Repository tag and arXiv v2 manuscript (must; only after the user reports the registration)

1. One question: the tag name (suggest `palomar-v1`) and where the verification statement goes in v2
   (end of §1, or a short "Formal verification" subsection before §11).
2. Create an annotated tag on the **registered** commit (message: Palomar entry ID/version, preflight run)
   and push it. Never move or delete it afterwards.
3. `validation/apply_edits.py`: v1 TeX + `confirmed` items of `edits.json` → `paper/…Updated.tex`; add the
   verification statement (D1 wording; names the platform contract; Palomar entry, repository URL, tag,
   commit) and one `biblio.bib` entry for the formalization. Build the v2 PDF; write `paper/v1-v2.diff`;
   `latexdiff paper/arxiv-v1/… paper/…` → `output/pdf/smctamper-v1-v2-latexdiff.pdf`.
4. `audit_errata.py --v2`: the diff is exactly the applied items plus the statement and bib entry; every
   sentence of the statement matches the registered Palomar statement (fidelity, D10).
5. Docs (not errata): README "Lean formalization" section and `CITATION.cff` get the Palomar ID and tag.
   Update `PALOMAR_SUBMISSION.md`. Hand v2 to the user, who uploads it to arXiv.

**Gate (= definition of done, §0):** tag pushed on the registered commit; v2 builds; v2 audit passes;
v2 PDF and latexdiff handed to the user.

---

## MVP path (if budget is tight)

R0 → R1 → R2 → R3 → R4 → R5 → R6 (no StateBound) → R8 → R9 → R10 → R11 → R12 → R13 → R14 → R15 →
(user registers) → R16, with `EmulationExact` (static L2 + unrolled L1), `SplitMemoryDetection`,
`HarvardSeparation`, `ClearAvoidance`, `TamperEvidence`. R7 and the *should/could* items are later Palomar
updates, not blockers (a later registry version does not move the R16 tag; it gets its own tag).

## Risks and fallbacks

| Risk | Fallback |
|---|---|
| 64-bit mask lemma (R2) resists `simp` | prove per `(j, op)` instance with `BitVec` ext over 64 concrete bit indices, or restate the C model through `rd64`/`wr8` with a separately proved bridge |
| Decoder too large or slow to elaborate | decode by first byte then ModRM; keep `decode` structural; prove only the instances used, by `rfl` |
| Symbolic execution of an iteration blows up | one lemma per instruction form with abstract register values; compose with `run_add`; case-split on the 4 opcodes once |
| 296-unit pass too heavy | generic unit lemma parameterised by `u` with layout lemmas from `Layout/Numbers`; induction on `u`; never instantiate all units |
| Self-modified displacement (R7) | keep R7 *should*; fallback claim = Level 1 + R5 byte equality |
| AsmJit encoder choice differs from §1 | trust the dump; update `Layout/AsmJitSize` and drop L05 |
| MASM chooses different jump sizes than AsmJit (static vs dynamic bytes differ) | keep two layout records; both must satisfy the Level-1 layout lemmas |
| Lake exceeds the memory cap locally | `build_modules.py` (direct `lean.exe` under the guard); cold builds in CI |
| Palomar policy requires something new | `refresh_policy.py`; change only workflow/schema pins, never Lean pins without asking |
| Author unavailable for `ask-author` items | record the item with both readings, choose the conservative wording, flag it in `ERRATA.md` |
| Challenge too large (ISA + images) | move images to layout data referenced by a short definition; select fewer Props (ask user) |

## Round-close checklist (copy into each `ROUNDS.md` entry)

- [ ] full build of `SmcTamper` green under the guard
- [ ] `axiom_audit.py` clean (only `propext`, `Quot.sound`, `Classical.choice`)
- [ ] round gate commands green; `validation/rounds/Rk.json` written
- [ ] `PAPER_MAP.md`, `edits.json` (`lean_refs`), `ROUNDS.md` handoff, `CLAUDE.md` current-round line updated
- [ ] committed (and pushed if authorised)
