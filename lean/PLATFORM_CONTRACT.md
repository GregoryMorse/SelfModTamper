# Platform contract (plan D2)

Windows and the CPU are black boxes. Every dependence on them is a field of a Lean structure or a hypothesis of a theorem
(never an `axiom`). This file lists each field: meaning, why it is plausible, source, evidence, and what is **not** claimed.
Items 3 and 4 (timers, scheduler/noise) are added in R10; the threat-model items in R11b/R11c. Final in R14.

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
  logical processor; that the intro's abstract instructions (`Contract/UnrolledStream`) have the real executed count `I`
  (`pass_clears_byte` needs `I ≥ 4`; `pass_clears_page` holds for every `I`).
