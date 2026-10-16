# Threat model (R11b–R11c; plan D11)

Status: R11b done (§1–§3). §4 onward (necessity witnesses, level matrix, scope witnesses, §10 replacement text) is R11c.

## 1. Model (`Spec/Threat.lean`)

* **System** `Sys`: original image `I0`, `n` checksum units (each a `CheckUnit` plus its own code set, response code set, threshold `tau`, native check time),
  protected addresses `prot`, SMC opcode bytes `ops` (vary legitimately, reset before each check), alarm parameter `k`.
* **Execution**: an infinite event stream `tl : Nat → TEv` (`exec`, `check` with a path, `write`, `splitWrite`, `dmaWrite`, `regWrite`, `idle`).
  The world holds a fetch view `F`, a data view `D` and a `split` flag. A check unit's schedule is `Sched` (`ck x m` = index of unit `x`'s `m`-th check).
* **Levels** L0–L4 (what an adversary may emit: `Level.allows`), timer source `tsc` / `osApi` (`Level.forgesReading`). Platform timing enters only as the
  cost contract `Cost` (lower bounds on emulation, debug-trap and mediation time), never as an axiom.
* **Goal**: `Wins` = a protected non-opcode byte is executed while the fetch view differs from `I0` (`ExecViolation`) and no effective alarm
  (`Alarm`: a value mismatch, or `k` consecutive timing failures, at a unit whose response code is intact) is ever raised.

## 2. Assumptions (`Assumptions`)

A1 coherence (no view separation); A2 coverage (every protected byte in some unit's region, unit code protected, strongly connected covers graph,
one unit never modified); A3 timing gap (native ≤ tau < emulation, trap and mediation lower bounds); A4 no physical (DMA) writer; A5 time integrity
(reading = elapsed); A6 persistence of a modification through the next `k` checks of each covering unit; A7 response code inside the unit's own code;
A8 non-compensation (a modification in an honest unit's region changes its result). None mentions alarm, wins or detection (`validation/threat_audit.py`).

## 3. Results (`Threat/`)

* `Timeline`: `last_write` (a differing fetch byte comes from a modifying write), `intact_code_orig`, `coherent_viewValue` (two-view value equals the Level-1 value).
* `Closure`: `closure_detect` (a modified unit reachable from an intact one forces a modification inside an intact unit's region).
* `Security`: `core_alarm`, **T1 `security`**: under `WF` and A1–A8, `¬ Wins`.
* `Levels`: `tsc_low_level`: levels below L2 with the inline timer give A1, A4, A5 from `WF.lvl`.
* `Witness`: the hypotheses are jointly satisfiable (`wAssumptions`, `witness_secure`). This checks consistency only.

## Caveats (recorded, not claimed away)

* The unrolled kernel's reset is argued, not proved separately; the intro length is abstract; page-granule counts are bounded above only.
* Emulation cost is a contract field (`emulLB`); the link to R8's `harvard_time_bound` is by argument, not a formal instance.
* A6 and A8 are structural properties of the design plus the schedule; their necessity witnesses (A8 forgery, A6 transient) are R11c.
* Literature pass (Collberg–Thomborson, Giffin, Chang–Atallah, Horne, Wurster, SWATT, Pioneer, Castelluccia, Kovah) and R-class platform facts
  (Intel SDM CR4.TSD, VMX RDTSC exiting, Microsoft Learn API notes) are deferred to R11c, where they are cited.
