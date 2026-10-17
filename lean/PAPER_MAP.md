# Paper map

Every claim of arXiv:2604.12407v1 with exactly one class (plan D1: F, FC, FD, M, R, X). `Status`: todo / done / open (open
obligations are listed at the end). `Declaration / evidence` is filled as rounds prove the claim. Seeded from plan section 5 in R1.

| ID | v1 location | Claim | Class | Round | Status | Declaration / evidence |
|---|---|---|---|---|---|---|
| C01 | §1 ¶1 | SMC on a deterministic machine can be simulated by non-SMC code (Harvard interpreter) | F | R8 | done | Harvard/Interp.lean `interp_step`, `interp_simulates` |
| C02 | Abstract, §1 ¶2, ¶4 | Timing-faithful non-SMC reproduction must read the code bytes it emulates; costlier under the cost contract | F + FC | R8 | done | Harvard/Separation.lean `harvard_reads_sensitive`, `harvard_time_bound` (cost contract as hypothesis) |
| C03 | §1 Model, §9 ¶1 | `P(T,C)` true iff code unmodified (overclaim, P04); corrected: completeness + conditional soundness | FC | R11a | done (FC) | Detection/Predicate.lean `P_complete`, `P_sound_value`, `P_sound_time`, `P_not_iff` (collision witness; P04 confirmed) |
| C04 | §1 Model (P08) | "constant-time kernels": control flow and instruction count are data-independent | F | R4, R6 | done at Level 1 and Level 2 (`unrolled_refines`, conditions in GAPS G01) | Static/Main.lean `constant_flow` (trace depends on ⌈ulSize/8⌉ only), `tpCompTrace`; Unrolled/Main.lean `unrolled_emulation`; Unrolled/L2Main.lean `unrolled_refines` |
| C05 | §1 Model | data stored as code (SMC-backed storage) is covered by the checksum | F | R11a | done (F) | Detection/Reset.lean `value_frame` (value determined by the covered bytes), `storage_tamper_detected` |
| C06 | §1 "Relation to prior work", §10 A1 | SMC checksumming detects memory-splitting (Harvard-mimicking) attacks that defeat plain self-checksumming; hence A1 | F | R8 | done (witness) | Harvard/SplitMemory.lean `split_differs_from_vn`, `smc_detects_fetch_patch`; mediation variant in R11c |
| C07 | §2 ¶1 | RDTSC/RDTSCP reliable statistically via repetition | FC | R10 | done (FC) | Contract/Noise.lean `undisturbed_exists` (repetition lemma), `sampleMin_le` |
| C08 | §2 ¶4–5 | coarse timers unsuitable for microbenchmarks (resolution) | FC | R10 | done (FC) | Contract/Timers.lean `reading_bounds`, `reading_indistinguishable`, `multimedia_min_inconsistent` (O1) |
| C09 | §2 ¶4 | Interrupt Time, QPC, precise UTC in the same precision class | FD | R10 | done (FD) | Data/Ratios.lean `c09_clocks_agree` (within 6 units) |
| C10 | §2, §3 | API/toolchain facts (Windows/Linux clocks, MSVC inline asm, `/SECTION`, `VirtualAlloc`, `mmap`) | R | R1 | done | R-class verified in R1 (table below) |
| C11 | §3 ¶5 | dynamic generation makes the monitored addresses contextual | F | R6 | done | Spec/Layout.lean `opOff`; `Unrolled/Sites` (296 distinct keys, shift by base) |
| C12 | §4 ¶1, ¶3 | modifying in-flight code triggers machine clears; naive SMC is slow | FC | R9 | done (FC) | Contract/StaticClears.lean `static_clears_ge`, `static_time_ge` |
| C13 | §4 ¶2 | unrolling + distinct pages reduce clears | FC | R9 | done (FC) | Contract/UnrolledClears.lean `pass_clears_page` (g = 4096: at most 2 ceil(W/8) per pass) |
| C14 | §4 ¶4 | detection granule → false positives | FC | R9 | done (FC) | Contract/Facts.lean `false_positive` |
| C15 | Table 1 | MSR/event identifiers (Intel, AMD) | R + M | R1, R12 | partial | see R-class table below |
| C16 | §4 ¶6 | PMCs only for measurement, not needed by the mechanism | M | R5 | done (M) | Layout/Scan.lean: no `0F 30/32/33/A2` byte pair in either 8123-byte loop image or in TPComp (scan of emitted bytes); the ISA subset contains none of these instructions |
| C17 | Table 2 | opcode pattern, bits 3–5, 2-bit toggle closure | F | R2 | done | Bits/Opcode.lean `table2_fields`, `opcodeOf_values`, `isOp_xor_toggle`, `opcodeOf_xor_toggle`, `kernelOpcode_xor_closed` |
| C18 | Table 2 | LAT/RCP values | R (P07) | R1 | partial | see R-class table below |
| C19 | Table 3 (P10) | instruction and condition-code semantics (S, G, P) | F + R | R3 | done | Spec/Step.lean (`aluW`, `cond`); X64/Step.lean: `cond_S`, `cond_P`, `cond_G`, `cond_L`, `aluW_adc_clear`, `aluW_sbb_clear`, `jg_after_cmp`; parity: Bits/Parity.lean |
| C20 | Fig. 2 | encodings in comments, `$-2-3-3-3-2-3` targets the ADC opcode | F + M | R3, R5 | done | X64/Facts.lean: `tpCompBytes_listing` (M: ml64 listing), `fig2_xor_targets_adc_opcode` |
| C21 | Fig. 3 | the C++ code emulates the SMC kernel precisely (with stated preconditions, P06) | F | R4 | done | Static/Emulation.lean `static_eq_c`; Static/Main.lean `static_emulation` (46 bytes on the ISA = `tpCompC`), `cIter_isOp` (default branch unreachable) |
| C22 | §5 ¶5 | RIP-relative addressing reaches nearby code without an address register | F + R | R3 | done | Spec/Step.lean `ripEA`; X64/Step.lean `exec_xorMB_mem`; X64/Facts.lean (Fig. 2 displacement) |
| C23 | §5 last ¶ | unrolling: emulator must track more sites as depth grows | F (should) | R6 | partial | `sites_nodup`, `sites_length` (`Unrolled/Sites`): D distinct sites for depth D; "harder to emulate" is not a theorem |
| C24 | §5 last ¶ | with suitable offset and depth, clears may disappear | FC | R9 | done (FC) | Contract/UnrolledClears.lean `g1_no_unit_clear`, `pass_clears_byte` (g = 1, W <= 1182, I >= 4) |
| C25 | Fig. 4 | snippet = 27-byte unit; `+1` skips the REX prefix | F + M | R3, R5 | done | X64/Facts.lean `unit_size_27`; Layout/Compare.lean `dyn_image_eq` (AsmJit bytes = 27-byte units), Layout/Targets.lean `unit_xor_target` |
| C26 | §6 ¶2 | sizes measured with placeholders equal the emitted sizes | F + M | R5 | done (M) | Layout/AsmJitSize.lean `intro_real`, `intro_measured`, `intro_cancellation` (model of AsmJit's immediate policy; evidence about the encoder, not a proof) |
| C27 | §6 ¶3 | dual-page layout: each unit writes the corresponding offset in the other page | F | R5, R6 | done | Layout/Numbers.lean `opcode_qwords_distinct`, `opOff_sep`; Layout/Targets.lean `unit_xor_target`, `unit_xor_other_page` |
| C28 | §6 ¶3 | branch-free termination by SMC; code restored afterwards | F | R6, R7 | done at Level 1 and Level 2 | Unrolled/Main.lean `unrolled_emulation` (patch applied, then restored); Unrolled/Facts.lean `next_byte_*`; Unrolled/L2Main.lean `unrolled_refines` (machine code: patch by the intro's self-modifying XOR, jump to the epilogue, restoration, store) |
| C29 | Fig. 5 (P03) | 148 units/page, intro 0x5F, unit 0x1B, base + size = end | F + FD + M | R5 | done (M) | Layout/Numbers.lean (`perPage_148`, `page1_fill`, `patch_target`, `bench_size_facts`, `fig5_sum`, `patch_xor`); Layout/Compare.lean (AsmJit and MASM bytes = Lean images); Layout/AsmJitSize.lean (intro 0x5F, cancellation) |
| C30 | §7 ¶1 | static SMC ≈ 7.9× slower | FD | R10 | done (FD) | Data/Ratios.lean `c30_static_ratio` |
| C31 | §7 ¶1–2 | heavy tail; minima stable; calibrate from quantiles | FC + X | R10, R11a | partial (FD done; quantile calibration R11a) | Data/Ratios.lean `c31_heavy_tail`; Contract/Noise.lean `sampleMin_le` |
| C32 | §7 ¶3 | dynamic ≈ 90.5× faster than non-SMC | FD | R10 | done (FD) | Data/Ratios.lean `c32_dynamic_ratio` |
| C33 | §7 ¶3 | ≈ 2.5× faster than static SMC (inconsistent, P02) | FD | R10 | done (FD) | Data/Ratios.lean `p02_no_ratio_2_5`, `p02_17_8` (P02 confirmed: no ratio is 2.5; 17.8) |
| C34 | §7 ¶3 | 3–4 pages no material improvement | X (data not reported) | R1 | done | listed as X (observation/opinion; nothing claimed) |
| C35 | §7 ¶4 | 246 runs / 2.5% / 3.6% estimate (P01) | FD + FC | R10 | done (FD + FC) | Contract/Estimator.lean `published_values`, `p01_smc`, `p01_nonsmc`, `p01_two_point_values`, `published_estimate_vacuous`, `markov_count`, `two_point` (P01 confirmed) |
| C36 | §7 ¶5, Table 6 | naive SMC clears ≫; unrolled reduced; clears at the start of unrolled iterations | FD + FC | R9 | done (FD + FC) | Contract/Table6.lean `table6_naive`, `table6_loop_page`, `table6_loop_byte_inconsistent`; Contract/Facts.lean `intro_stores`, `tail_stores` |
| C37 | Tables 4–5 | cross-timer consistency (TSC ≈ 2.59 GHz) | FD | R10 | done (FD) | Data/Ratios.lean `c37_tsc_over_clock` (259.0-259.3 cycles per 100 ns) |
| C38 | Tables 4–5 | measured interval contents (P05) | M | R12 | done (evidence only) | R12 pre-fix binary: label order L01, console write and driver call inside the timed interval L02 (`SelfModTamper.cpp`); pattern check in `validation/data/native_runs.json`; no proof |
| C39 | §8 ¶1 | `c_nonSMC O(n) ≫ c_SMC O(n)` (notation, P09) | FD + X | R10 | done (FD) | Data/Ratios.lean `c39_cycles_per_qword` (10168 vs 112); notation fix P09 |
| C40 | §8 ¶2 | optimality hard, combinatorial; compilers can beat hand asm | X | R1 | done | listed as X (observation/opinion; nothing claimed) |
| C41 | §8 ¶3 | Pentium III remark; branching expensive | X | R1 | done | listed as X (observation/opinion; nothing claimed) |
| C42 | §8 ¶3 | design rule: never modify the currently executing page | FC | R9 | done (FC) | Contract/Facts.lean `no_clear_of_disjoint` |
| C43 | §8 ¶3 | task switches dominate perturbation; priority mitigates | FC + X | R10 | done (FC; priority remark X) | Contract/Noise.lean `maxInterrupts_mono`, `undisturbed_exists` |
| C44 | §9 ¶1 | many units; validation state machine; reset bounds state growth | F | R11a | done (F) | Detection/Reset.lean `reset_restores`, `reset_value_stable`, `no_reset_value_depends_on_calls` (`Unrolled/Reset` `reset_restores_unrolled`, `reset_value_stable_unrolled` for the unrolled kernel at Level 1) |
| C45 | §9 ¶2 | thresholds from quantiles; k consecutive failures | FC | R11a | done (FC) | Detection/Policy.lean `no_false_alarm`, `alarm_of_persistent`, `calibration_no_alarm` |
| C46 | §10 | A1–A4 scope the model; corrected: the complete threat model A1–A8 with T1–T4 (D11, P11) | F + FC | R11b, R11c | done (R11c, see notes below) | Threat/Security.lean `security` (T1), `closure_detect`, `core_alarm`; Threat/Witness.lean `witness_secure`; Threat/T3.lean `T3`; Threat/T3full.lean `T3_full`; Threat/Matrix.lean `T4`; P11 text in `edits.json` |
| C47 | §10 ¶2 | reconfigurable hardware compatible; not attestation | X | R1 | done | listed as X (observation/opinion; nothing claimed) |
| C48 | §11 | summary restates C12–C45 | X (summary; discharged through its referents C12-C45) | R14 | done | listed as X: restates C12-C45, nothing new is claimed |
| C49 | §10 A1 | von Neumann needed; pure Harvard outside. Corrected: coherence; SMC detects split views or forces costly mediation (T2) | F + FC | R8, R11c | done (R11c, see notes below) | Threat/SplitMirror.lean `faithful_needs_med`, `mediated_timefail` (T2, scope in THREAT_MODEL section 3); `nec_A1` |
| C50 | §10 A2, §9 ¶1 | units cannot all be neutralised; many units. Corrected: structural coverage + one intact unit (T1); neutralise-all witness (T3) | F | R11b, R11c | done (R11c, see notes below) | `nec_A2cov`, `nec_A2intact`, `nec_A2code`, `nec_A2conn` (Threat/Witnesses*, T3full) |
| C51 | §10 A3 | no equally fast faithful non-SMC implementation. Corrected: calibration condition under the cost contract (T1); emulation-under-τ witness (T3) | FC | R11b, R11c | done (R11c, see notes below) | `nec_A3` (emulation under tau) |
| C52 | §10 A4 | DMA/FPGA need a larger-area defense. Corrected: write–use race exists for every schedule with a gap (T3) | F | R11c | done (R11c, see notes below) | `nec_A4` (write-use race for every schedule with a gap) |
| C53 | §1 "Relation to prior work" | local assurance without a remote verifier. Consequence: time source on the untrusted host; guarantees for ≤ L1 (T4) | FC + R | R11c | done (R11c, see notes below) | Threat/Matrix.lean `T4`, `ext_clock_detects` |
| C54 | §1 "Practical stance" | a synthetic time source requires a full timing model (false: replay suffices, P13) | F | R11c | done (R11c, see notes below) | `nec_A5`, `nec_A5_osApi` (P13) |
| C55 | §1 "External inputs" | the scheme protects against debugging, thread injection, remote writes (qualified, P12) | F | R11c | done (R11c, see notes below) | `injected_code_outside_goal`, `nec_A6` (P12) |
| C56 | §5 ¶2 | checksum not collision resistant; protection from dynamic state and timing (made precise by A8 and the forgery theorem) | F | R11c | done (R11c, see notes below) | `nec_A8`, `forgery_value`, `two_not_enough` (P04 pair; Threat/Forgery.lean) |

## R-class verification (R1, 2026-10-15)

| Claim | Source checked | Result |
|---|---|---|
| C10 `GetSystemTimePreciseAsFileTime`, `QueryPerformanceCounter`, `QueryInterruptTimePrecise`, `GetTickCount64`, `timeGetTime`, `VirtualAlloc` | Microsoft Learn pages under learn.microsoft.com/en-us/windows/win32/api/ (sysinfoapi, profileapi, realtimeapiset, timeapi, memoryapi): all resolve (HTTP 200) | the APIs exist with the described purposes; resolution classes are not re-derived (the data are FD) |
| C10 MSVC inline assembly x86-only; `/SECTION:.text,RWE` | learn.microsoft.com/en-us/cpp/assembler/inline/inline-assembler (x64 not supported), /cpp/build/reference/section-specify-section-attributes | consistent with the text |
| C10 Linux `clock_gettime` clocks (`CLOCK_REALTIME`, `CLOCK_MONOTONIC`, `CLOCK_BOOTTIME` since 2.6.39), `mmap`, `perf_event_open` | man7.org man pages clock_gettime(2), mmap(2), perf_event_open(2) | consistent with the text |
| C10 "AVR32, SPARC V9, PowerPC, ARMv7, ARMv8 provide counter-style instructions" | not checked | class X (passing remark, nothing depends on it) |
| C15 Intel: MSR 0x38F, 0x186, 0xC1; event C3H / umask 04H `MACHINE_CLEARS.SMC` | Linux perf JSON (tools/perf/pmu-events/arch/x86/skylake/pipeline.json: EventCode 0xC3, UMask 0x4, MACHINE_CLEARS.SMC); MSR numbers IA32_PERF_GLOBAL_CTRL 38FH, IA32_PERFEVTSEL0 186H, IA32_PMC0 0C1H (Intel SDM Vol. 4) from the author's knowledge, not re-fetched | event values verified; MSR numbers standard |
| C15 AMD: MSR C000_0301, C001_0000, C001_0004; PMCx021 | Linux perf JSON for amdzen1-5 has no self-modifying-code event; AMD PPR text for PMCx021 could not be retrieved | OPEN (P14, ask-author): the AMD column is unverified; the author's 2012 copy of AMD64 APM Vol. 2 (rev 3.21) confirms MSRs C001_0000 PerfEvtSel0 and C001_0004 PerfCtr0 but contains neither C000_0301 nor event 0x21 (the paper cites the January 2023 revision, not available here); BKDG/PPR downloads failed. Earlier note: (event 0x21 is named as a Family 10h-era event; Table 1's caption says "representative supported microarchitectures"). The author asked that unreferenced data be corrected: needs the 2023 APM or a PPR/BKDG. See QUESTIONS.md |
| C18 Table 2 LAT/RCP | uops.info measurements for the r64,m64 forms (Skylake, Zen 3); AsmGrid (interactive page, not readable here) | CMP LAT 0.2/0.25 is not a latency (uops.info: 1 cycle); ADD r64,m64 throughput measures 1.0 on Skylake, the printed RCP 0.25 describes another form. Recorded as P07 (confirmed by the author: CMP LAT = 1) |

## Notes from the R1 scan for further quantitative errors

* Table 2 opcode column and Opcode[3:5] column are consistent: (opcode >> 3) & 7 = 2,0,4,7,1,3,5,6 for ADC, ADD, AND, CMP, OR, SBB, SUB, XOR. Verified by hand in R1; proved in R2.
* Fig. 3 `preserve = ~(5ULL << pModByteOffset)` clears bits 0 and 2 of the 3-bit opcode field; with the base field 2 (ADC) the substituted field is 2 | op in {2,3,6,7} = {ADC,SBB,XOR,CMP}. Consistent. R2/R4 prove it.
* Table 3 condition-code semantics (S: SF=1, G: ZF=0 and SF=OF, P: PF=1) match the Intel SDM Jcc/SETcc tables.
* No further quantitative error found in Sections 2-9 besides P01-P09; Table 1, Table 6 and Figure 5 values are transcribed in `validation/data/paper_tables.json` and consistent with the arithmetic in plan section 1.

## Open obligations

* C15 AMD column (P14): primary source for MSR C000_0301 and PMCx021 not yet found.

R2 also proved (support for C21, R4): SmcTamper.cSubst_eq_setByte (the Fig. 3 `preserve`/shift substitution replaces exactly byte j by `opcodeOf op`), rd64_wr8_outside / rd64_wr8_inside / rd64_wr8_aligned (Bits/Bytes.lean).

R11b (threat model I): T1 `Threat/Security.lean` `security` (no win under A1–A8 and the cost contract), `closure_detect`, `core_alarm`; hypothesis consistency
`Threat/Witness.lean` `witness_secure`; `Threat/Levels.lean` `tsc_low_level`. §10 rows (P11, P12, P13) remain open until R11c; see `lean/THREAT_MODEL.md`.

R11c rows: C46 sec 10 -> P11 text in `edits.json` (Threat.Security/T3/Matrix); C49 sec 10 A1 -> `nec_A1`, `faithful_needs_med` (T2 scoped, see THREAT_MODEL section 3); C50 sec 10 A2 -> `nec_A2cov`, `nec_A2intact`;
C51 sec 10 A3 -> `nec_A3`; C52 sec 10 A4 -> `nec_A4`; C53 sec 1 prior work -> `T4`, `ext_clock_detects`; C54 sec 1 synthetic clock -> `nec_A5` (P13); C55 sec 1 external inputs -> `injected_code_outside_goal`, `nec_A6` (P12);
C56 sec 5 collisions -> `nec_A8` (P04 pair). Open obligations: A2 code/connectivity and A7 necessity witnesses; 3-qword forgery theorem; SDM VMX/EPT/DR facts to be read from primary text before the v2 manuscript cites them.
