# Threat model (R11b–R11c; plan D11)

Everything below is stated relative to the Lean model in `lean/SmcTamper/Spec/Threat.lean`. Platform behaviour is a contract field,
never a proved fact about hardware. Evidence is not proof; nothing here claims more than the Lean hypotheses give.

## 1. Model (`Spec/Threat.lean`)

* **System** `Sys`: original image `I0`, `n` checksum units (each a `CheckUnit` plus its own code set, response code set, threshold `tau`,
  native check time), protected addresses `prot`, SMC opcode bytes `ops` (vary legitimately, reset before each check), alarm parameter `k`.
* **Execution**: an infinite event stream `tl : Nat → TEv` (`exec`, `check` with a path, `write`, `splitWrite`, `dmaWrite`, `regWrite`, `idle`).
  The world holds a fetch view `F`, a data view `D` and a `split` flag. A unit's schedule is `Sched` (`ck x m` = index of unit `x`'s `m`-th check).
* **Levels** L0–L4 (`Level.allows`), timer source `tsc` / `osApi` (`Level.forgesReading`). Timing enters only as the cost contract `Cost`
  (`emulLB`, `kd`, `km`: lower bounds on emulation, debug trap, mediation).
* **Goal**: `Wins` = a protected non-opcode byte is executed while the fetch view differs from `I0` (`ExecViolation`) and no effective alarm
  (`Alarm`: a value mismatch, or `k` consecutive timing failures, at a unit whose response code is intact).

## 2. Assumptions (`Assumptions`; named defs `A1`…`A8`)

| # | Lean | Statement | Replaces in v1 |
|---|------|-----------|----------------|
| A1 | `A1` | fetch and data views are one image throughout | "von Neumann architecture" |
| A2 | `A2cov`, `A2code`, `A2conn`, `A2intact` | every protected byte in some unit's region; unit code protected; covers graph strongly connected; one unit never modified | "cannot neutralize all functions" |
| A3 | `A3` | native ≤ τ < emulation / debug-trap / mediation lower bounds | "no equally fast non-SMC implementation" |
| A4 | `A4` | no writer outside the protected thread (DMA) | "larger-area defense" remark |
| A5 | `A5` | every reading equals the elapsed time | missing |
| A6 | `A6` | a modification persists through the next `k` checks of each covering unit | missing |
| A7 | `A7` | response code lies in the unit's own protected code | missing |
| A8 | `A8` | a modification in an honestly running unit's region changes its result | missing ("not collision resistant") |

None mentions alarm, wins or detection (`validation/threat_audit.py`).

## 3. Results

* **T1** `security` (`Threat/Security`): under `WF` and A1–A8, `¬ Wins`. Proof: `closure_detect` (a modification reaches an intact unit's
  region), `core_alarm` (first check after the write, A6 persistence, A8 value mismatch on the honest path, A3+A5 timing failure otherwise).
  `witness_secure` shows the hypotheses are jointly satisfiable.
* **T2** `Threat/SplitMirror`: `faithful_needs_med` (a run following the Level-1 trajectory under split views needs a mediation at every
  opcode-changing, non-final iteration), `mediated_timefail` (with A3, A5 such a check is a timing failure). **Scope:** this covers the SMC
  kernel's own opcode state. A modification of a byte that the kernel only *reads* is invisible under split views whether or not the kernel is
  self-modifying (`nec_A1` uses a toggle-free kernel; the same read path applies to any kernel). T2 therefore does *not* say "T1 holds without A1".
  An unfaithful (un-mirrored) run is a different computation; whether its value matches is A8 for that run.
* **T3** `Threat/T3` (`T3`, `necessary_A*`): for A1, A2-coverage, A2-intact, A3, A4, A5, A6, A8, a system and timeline satisfying `WF` and all other
  assumptions (`AllBut i`) in which the adversary wins; `not_holds` derives that the dropped assumption fails (T1 contrapositive).
  Witnesses: A1 split write against a toggle-free kernel; A2cov a protected byte outside every region; A2intact the only unit neutralised;
  A3 `emulLB = 0`; A4 DMA write–use–restore; A5 replayed reading `1` with elapsed `100` (L2 clock, and L1 with an OS timer); A6 write–use–restore
  between checks; A8 the two-quadword collision `0 ↔ 0x8000000000000001` (P04 pair, kernel ADC→CMP).
  `Threat/T3full` (`T3_full`) adds A7 (the response byte lies outside the unit's code and is modified; all checks are emulated, no alarm is effective), A2 code protected
  and A2 strong connectivity (two units, a periodic timeline `Threat/Loop`: unit 1 is neutralised while its unprotected code byte is set, which unit 0 never sees, or unit 0 does not cover unit 1).
  `Threat/Forgery` (A8 necessity, P04): `forgery_three` (from any kernel state, three adversary-chosen quadwords reach every target an honest run reaches),
  `two_not_enough` (the target `(2^63+1, XOR)` is not reachable in two quadwords from the canonical state), `forgery_value` (for a unit with at least three quadwords and the opcode byte
  outside the region, any tampering of the earlier quadwords is compensated by the last three: the unit's value is the honest one), via `tpCompC_abs` and `static_eq_c`.
  The unreachable state is `(S, CMP)` with `toggle S = 0` (`HInv`, `reachable_inv`).
* **T4** `Threat/Matrix`: `tsc_low_level` (L0/L1 with the inline timer give A1, A4, A5), `nec_A5_osApi` (L1 with an OS timer API can forge
  readings), L2 breaks A1 and A5, L4 breaks A4, `ext_clock_detects` (external clock, resolution `r`, jitter `j`: slowdowns ≥ `j+2r` exceed the calibrated
  threshold; `reading_indistinguishable` shows slowdowns < `r` can be invisible).
* **Scope** `Threat/Scope`: `injected_code_outside_goal` (all assumptions hold, malicious code outside the protected range executes, no violation);
  `noeffect_events` (register writes are not modelled).

## 4. Level capabilities and their sources (contract fields)

Verified this session (primary pages fetched):

* `WriteProcessMemory` — needs `PROCESS_VM_WRITE` and `PROCESS_VM_OPERATION` on the process handle (Microsoft Learn, memoryapi.h): L1 write.
* `SetThreadContext` — needs `THREAD_SET_CONTEXT`; "do not try to set the context for a running thread, suspend first": register tampering at L1.
* `CreateRemoteThread` — needs `PROCESS_CREATE_THREAD`, `PROCESS_QUERY_INFORMATION`, `PROCESS_VM_OPERATION`, `PROCESS_VM_WRITE`, `PROCESS_VM_READ`;
  the documentation says it "changes the timing and memory layout of the process": thread injection at L1.
* `CR4.TSD` — when set, `RDTSC` is restricted to privilege level 0 (#GP(0) otherwise) (Intel SDM RDTSC page, via a mirror; secondary source).

**Not verified this session (named only, no claim depends on their text):** VMX "RDTSC exiting" / "use TSC offsetting" controls (SDM Vol. 3C ch. 25),
EPT execute-only pages, debug registers DR0–DR7 and #DB. They justify the `Level.forgesReading` / `Level.allows` entries for L2 and above. Before the
v2 manuscript cites them, read the SDM sections directly (open obligation).

## 5. Literature (DOIs, titles, authors, venues and years verified against Crossref this session; text of the papers not re-read)

| Work | DOI | Role here |
|------|-----|-----------|
| Collberg, Thomborson, *Watermarking, tamper-proofing, and obfuscation — tools for software protection*, IEEE TSE 2002 | 10.1109/tse.2002.1027797 | taxonomy; tamper-proofing as detection plus response (cited in v1) |
| Chang, Atallah, *Protecting software code by guards*, LNCS 2002 (DRM 2001) | 10.1007/3-540-47870-1_10 | mutually checking guards ↔ A2 covers graph |
| Horne, Matheson, Sheehan, Tarjan, *Dynamic self-checking techniques for improved tamper resistance*, LNCS 2002 (DRM 2001) | 10.1007/3-540-47870-1_9 | redundant small testers ↔ A2 coverage |
| Giffin, Christodorescu, Kruger, *Strengthening software self-checksumming via self-modifying code*, ACSAC 2005 | 10.1109/csac.2005.53 | SMC against the split-memory attack ↔ A1, T2 (cited in v1) |
| Wurster, van Oorschot, Somayaji, *A generic attack on checksumming-based software tamper resistance*, IEEE S&P 2005 | 10.1109/sp.2005.2 | view-separation attack ↔ L2, A1 |
| Seshadri, Perrig, van Doorn, Khosla, *SWATT*, IEEE S&P 2004 | 10.1109/secpri.2004.1301329 | timing-based attestation with a verifier's clock ↔ A5 |
| Seshadri, Luk, Shi, Perrig, van Doorn, Khosla, *Pioneer*, SOSP 2005 | 10.1145/1095810.1095812 | same, for code integrity on commodity hosts |
| Castelluccia, Francillon, Perito, Soriente, *On the difficulty of software-based attestation of embedded devices*, CCS 2009 | 10.1145/1653662.1653711 | attacks on timing-based attestation ↔ A3 calibration |
| Kovah, Kallenberg, Weathers, Herzog, Thomas, *New results for timing-based attestation*, IEEE S&P 2012 | 10.1109/sp.2012.45 | measuring timing attestation on x86 ↔ A3, A5 |

Which assumptions are standard and which are new: A1 and the split-view attack are in Wurster et al. and Giffin et al.; A5 is the standard requirement of
timing-based attestation (an outside clock); A2, A6, A7, A8 are made explicit here; the necessity witnesses are new to this development. The "role" column is
from the titles and general knowledge of the papers, not from re-reading them.

## 6. Caveats (recorded, not claimed away)

* The unrolled kernel's reset is argued, not proved separately; the intro length is abstract; page-granule counts are bounded above only.
* Emulation cost is a contract field (`emulLB`); the link to R8's `harvard_time_bound` is by argument, not a formal instance.
* The model has one fetch view and one data view; the kernel's reads come from the data view. Hence T2 as above.
* `Level.allows` for L0 allows only an initial run of writes; L3 has no extra events and is reserved.
* Witness systems are tiny (one unit, region 8 or 16 bytes); they show necessity, not realism.
