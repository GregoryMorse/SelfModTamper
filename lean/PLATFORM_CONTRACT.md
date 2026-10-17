# Platform contract (plan D2)

Windows and the CPU are black boxes. Every dependence on them is a field of a Lean structure or a hypothesis of a theorem
(never an `axiom`). This file lists each field: meaning, why it is plausible, source, evidence, and what is **not** claimed.
Final (R14).

## 1. ISA model (a definition, not a hypothesis)

- **What:** `Spec/ISA.lean`, `Spec/Step.lean`: an x86-64 subset (decode from the *current* memory bytes, then execute). Fetching
  from current memory is the architectural behaviour for a thread modifying its own code (Intel SDM Vol. 3A, "Handling
  Self- and Cross-Modifying Code").
- **Evidence (M-class):** the byte images produced by MASM and AsmJit equal the Lean encodings (`Layout/Compare.lean`);
  `ml64` listings (`X64/Facts.lean`). These show the *encodings* are right; they do not show the silicon implements the model.
- **Not claimed:** nothing about microarchitectural state, ordering of other threads, or serialisation on other processors.

## 2. Clear contract `ClearRule g W κ` (`Spec/Contract.lean`)

- **What:** a store triggers a machine clear iff one of the next `W` executed instructions has a byte in the same `g`-byte
  granule as a byte of the store; each clear costs `κ` cycles above an unknown base cost (`clearTime`).
  `g = 1` byte-exact, `64` cache line, `4096` page. `W` models the in-flight window; the proofs quantify over every `W` (the paper states none).
- **Why plausible:** the paper (§4) says the processor detects SMC at page or smaller granularity and squashes in-flight
  instructions; the contract is the simplest model with those two parameters.
- **Evidence (FD, not proof):** `Contract/Table6.lean` checks that, for `g = 4096`, the model's upper bound on clears per run reaches the
  Table 6 count only if `W ≥ 105` (unrelated events allowed up to the `C Loop` count), and that `g = 1` with `W ≤ 1182`
  cannot reach it. The bound is an upper bound, so this is a necessary condition, not a fit.
  This is a statement about the model's fit to the printed counts, not a measurement of the CPU. The performance event counted
  in Table 6 (`MACHINE_CLEARS.SMC`) may count more than one event per clear (the naive kernel shows two per iteration).
- **Theorems that use it:** `static_clears_ge` (C12, `g ≥ 1`, `W ≥ 4`), `pass_clears_byte` (C24), `pass_clears_page` (C13),
  `false_positive` (C14), `no_clear_of_disjoint` (C42).
- **Not claimed:** that real processors follow this rule; an exact `W`; behaviour for self-modification of code on a different
  logical processor; that the machine executes the stream `Contract/UnrolledStream` as modelled. The intro count is derived, not assumed: the Level-2 run of a pass
  executes `passLen = periodOf 3` instructions (`Unrolled/IntroCount`), so `I = 3` and `pass_clears_byte_real` holds for windows `W ≤ 1181`.

## 3. Timer contract (`Contract/Timers.lean`)

- **What:** a timer is a counter of resolution `r > 0` and unknown phase `φ`; the reading of `[s, e)` is
  `⌊(e+φ)/r⌋ − ⌊(s+φ)/r⌋` (`reading`).
- **Proved from it:** a reading of length `d` is `⌊d/r⌋` or `⌊d/r⌋ + 1` (`reading_bounds`); intervals differing by less than `r`
  can read alike (`reading_indistinguishable`).
- **Evidence (FD):** Tables 4–5 are consistent with `Interrupt Time`, `Perf. Counter`, `Precise UTC` having the same resolution
  class (`Data/Ratios.c09_clocks_agree`) and with the TSC at about `2.59 GHz` against them (`c37_tsc_over_clock`); the printed
  `Multimedia` minimum (1 ms) cannot come from runs of at least 2.8806 ms under this contract (`multimedia_min_inconsistent`,
  observation O1, not an erratum).
- **Not claimed:** how any Windows or CPU timer is implemented; that readings come from the same runs.

## 4. Scheduler and noise contract (`Contract/Noise.lean`)

- **What:** per run of length `L` at most `⌊L/q⌋ + 1` clock interrupts (`maxInterrupts`); a run is *disturbed* when its noise
  exceeds a threshold; deterministic repetition assumption: of any `k` consecutive runs at most `r < k` are disturbed.
- **Proved from it:** some run in every window of `k` is undisturbed (`undisturbed_exists`); the minimum of a sample is at most
  every sample (`sampleMin_le`); the number of runs above the minimum is at least `N (avg − min)/(max − min)` for integer
  statistics `avg = ⌊Σ/N⌋` (`Contract/Estimator.count_above_min_lower`), which replaces the printed estimate
  `N (avg − min)/max` (that is Markov's bound at `θ = max`, an empty set: `published_estimate_vacuous`).
- **Not claimed:** an i.i.d. noise model; that the plan's priority mitigation (C43) works (class X, a remark).

## 5. Threat-model contract (`Spec/Threat.lean`; `THREAT_MODEL.md` has the argument)

- **Cost contract `Cost`** (`emulLB`, `kd`, `km`): lower bounds on the elapsed time of an emulated check, of a debug-trap-forged check,
  and per mediated (split-view) iteration. `Cost.admits` makes them constraints on the adversary's timeline. *Plausible:* an emulation
  has to read the bytes it emulates (C02, `harvard_reads_sensitive`) and a debug trap or a view switch costs cycles. *Instance:*
  `Threat/EmulBound` derives `emulLB` from the Harvard bound given a per-read charge `ρ`; the charge and which bytes are sensitive are
  hypotheses. *Not claimed:* any numeric value for any real CPU, hypervisor or Windows version.
- **Level contract `Level.allows` and `WF`:** what an adversary at each of L0..L4 may emit (writes, split views, timer forgery, DMA) and
  that honest/neutral/mediated check paths mean what their names say (`WF.honestCode`, `neutralMod`, `medSplit`). *Plausible:* the
  level table of `THREAT_MODEL.md` section 4. *Not claimed:* that a real system's levels are separated this way (L3 adds nothing
  beyond L2, `Threat/LevelMono`).
- **Assumptions A1-A8** are structural conditions on the timeline and system (no split views, covering units, intact unit, timing gap,
  no DMA, time integrity, persistence, response coverage, non-compensation), never "the attacker is detected" (`validation/threat_audit.py`).
  Each is necessary: `T3_full` gives a winning adversary when exactly one is dropped. *Not claimed:* that a deployed system meets any of
  them; A5 in particular fails with an OS timer API (T4) or at L2.
- **Not modelled:** speculative execution, other logical processors, instruction-cache replay, hardware debug registers (named in
  `THREAT_MODEL.md` but not read from the primary manuals, G21), reconfigurable hardware.

## 6. Non-claims (gap register G01-G05)

- The unrolled kernel is verified at Level 1 (an abstract machine whose opcode state lives in the memory the kernel reads), the byte
  layout against the assembler output, and at Level 2: `unrolled_refines` runs the x86-64 model on the image bytes (patch and restoration included)
  and gets `callUnrolled`, under the hypotheses of GAPS G01 (the qword count of the final pass is not a multiple of 148). Not claimed: that a real processor executes these instructions as the model does (the model is
  the contract of section 1).
- Exact machine-clear counts are not proved (only the upper bounds and the consistency checks against Table 6, G04); no line-granule
  (g = 64) figure is claimed (G05).
- The kernels crash when the qword count is a multiple of 148 (defect L07); the product guards it (CODE_FIXES L07) and the native vectors avoid those sizes. No Lean theorem models the crash.
