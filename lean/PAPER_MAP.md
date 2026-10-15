# Paper map

Every claim of arXiv:2604.12407v1 with exactly one class (plan D1: F, FC, FD, M, R, X). `Status`: todo / done / open (open
obligations are listed at the end). `Declaration / evidence` is filled as rounds prove the claim. Seeded from plan section 5 in R1.

| ID | v1 location | Claim | Class | Round | Status | Declaration / evidence |
|---|---|---|---|---|---|---|
| C01 | §1 ¶1 | SMC on a deterministic machine can be simulated by non-SMC code (Harvard interpreter) | F | R8 | todo |  |
| C02 | Abstract, §1 ¶2, ¶4 | Timing-faithful non-SMC reproduction must read the code bytes it emulates; costlier under the cost contract | F + FC | R8 | todo |  |
| C03 | §1 Model, §9 ¶1 | `P(T,C)` true iff code unmodified (overclaim, P04); corrected: completeness + conditional soundness | FC | R11a | todo |  |
| C04 | §1 Model | "constant-time kernels": control flow and instruction count are data-independent | F | R4, R6 | todo |  |
| C05 | §1 Model | data stored as code (SMC-backed storage) is covered by the checksum | F | R11a | todo |  |
| C06 | §1 "Relation to prior work", §10 A1 | SMC checksumming detects memory-splitting (Harvard-mimicking) attacks that defeat plain self-checksumming; hence A1 | F | R8 | todo |  |
| C07 | §2 ¶1 | RDTSC/RDTSCP reliable statistically via repetition | FC | R10 | todo |  |
| C08 | §2 ¶4–5 | coarse timers unsuitable for microbenchmarks (resolution) | FC | R10 | todo |  |
| C09 | §2 ¶4 | Interrupt Time, QPC, precise UTC in the same precision class | FD | R10 | todo |  |
| C10 | §2, §3 | API/toolchain facts (Windows/Linux clocks, MSVC inline asm, `/SECTION`, `VirtualAlloc`, `mmap`) | R | R1 | done | R-class verified in R1 (table below) |
| C11 | §3 ¶5 | dynamic generation makes the monitored addresses contextual | F | R6 | todo |  |
| C12 | §4 ¶1, ¶3 | modifying in-flight code triggers machine clears; naive SMC is slow | FC | R9 | todo |  |
| C13 | §4 ¶2 | unrolling + distinct pages reduce clears | FC | R9 | todo |  |
| C14 | §4 ¶4 | detection granule → false positives | FC | R9 | todo |  |
| C15 | Table 1 | MSR/event identifiers (Intel, AMD) | R + M | R1, R12 | partial | see R-class table below |
| C16 | §4 ¶6 | PMCs only for measurement, not needed by the mechanism | M | R5 | todo |  |
| C17 | Table 2 | opcode pattern, bits 3–5, 2-bit toggle closure | F | R2 | todo |  |
| C18 | Table 2 | LAT/RCP values | R (P07) | R1 | partial | see R-class table below |
| C19 | Table 3 | instruction and condition-code semantics (S, G, P) | F + R | R3 | todo |  |
| C20 | Fig. 2 | encodings in comments, `$-2-3-3-3-2-3` targets the ADC opcode | F + M | R3, R5 | todo |  |
| C21 | Fig. 3 | the C++ code emulates the SMC kernel precisely (with stated preconditions, P06) | F | R4 | todo |  |
| C22 | §5 ¶5 | RIP-relative addressing reaches nearby code without an address register | F + R | R3 | todo |  |
| C23 | §5 last ¶ | unrolling: emulator must track more sites as depth grows | F (should) | R6 | todo |  |
| C24 | §5 last ¶ | with suitable offset and depth, clears may disappear | FC | R9 | todo |  |
| C25 | Fig. 4 | snippet = 27-byte unit; `+1` skips the REX prefix | F + M | R3, R5 | todo |  |
| C26 | §6 ¶2 | sizes measured with placeholders equal the emitted sizes | F + M | R5 | todo |  |
| C27 | §6 ¶3 | dual-page layout: each unit writes the corresponding offset in the other page | F | R5, R6 | todo |  |
| C28 | §6 ¶3 | branch-free termination by SMC; code restored afterwards | F | R6, R7 | todo |  |
| C29 | Fig. 5 | 148 units/page, intro 0x5F, unit 0x1B, base + size = end | F + FD + M | R5 | todo |  |
| C30 | §7 ¶1 | static SMC ≈ 7.9× slower | FD | R10 | todo |  |
| C31 | §7 ¶1–2 | heavy tail; minima stable; calibrate from quantiles | FC + X | R10, R11a | todo |  |
| C32 | §7 ¶3 | dynamic ≈ 90.5× faster than non-SMC | FD | R10 | todo |  |
| C33 | §7 ¶3 | ≈ 2.5× faster than static SMC (inconsistent, P02) | FD | R10 | todo |  |
| C34 | §7 ¶3 | 3–4 pages no material improvement | X (data not reported) | R1 | done | listed as X (observation/opinion; nothing claimed) |
| C35 | §7 ¶4 | 246 runs / 2.5% / 3.6% estimate (P01) | FD + FC | R10 | todo |  |
| C36 | §7 ¶5, Table 6 | naive SMC clears ≫; unrolled reduced; clears at the start of unrolled iterations | FD + FC | R9 | todo |  |
| C37 | Tables 4–5 | cross-timer consistency (TSC ≈ 2.59 GHz) | FD | R10 | todo |  |
| C38 | Tables 4–5 | measured interval contents (P05) | M | R12 | todo |  |
| C39 | §8 ¶1 | `c_nonSMC O(n) ≫ c_SMC O(n)` (notation, P09) | FD + X | R10 | todo |  |
| C40 | §8 ¶2 | optimality hard, combinatorial; compilers can beat hand asm | X | R1 | done | listed as X (observation/opinion; nothing claimed) |
| C41 | §8 ¶3 | Pentium III remark; branching expensive | X | R1 | done | listed as X (observation/opinion; nothing claimed) |
| C42 | §8 ¶3 | design rule: never modify the currently executing page | FC | R9 | todo |  |
| C43 | §8 ¶3 | task switches dominate perturbation; priority mitigates | FC + X | R10 | todo |  |
| C44 | §9 ¶1 | many units; validation state machine; reset bounds state growth | F | R11a | todo |  |
| C45 | §9 ¶2 | thresholds from quantiles; k consecutive failures | FC | R11a | todo |  |
| C46 | §10 | A1–A4 scope the model; corrected: the complete threat model A1–A8 with T1–T4 (D11, P11) | F + FC | R11b, R11c | todo |  |
| C47 | §10 ¶2 | reconfigurable hardware compatible; not attestation | X | R1 | done | listed as X (observation/opinion; nothing claimed) |
| C48 | §11 | summary restates C12–C45 | X (summary; discharged through its referents C12-C45) | R14 | todo | refs only |
| C49 | §10 A1 | von Neumann needed; pure Harvard outside. Corrected: coherence; SMC detects split views or forces costly mediation (T2) | F + FC | R8, R11c | todo |  |
| C50 | §10 A2, §9 ¶1 | units cannot all be neutralised; many units. Corrected: structural coverage + one intact unit (T1); neutralise-all witness (T3) | F | R11b, R11c | todo |  |
| C51 | §10 A3 | no equally fast faithful non-SMC implementation. Corrected: calibration condition under the cost contract (T1); emulation-under-τ witness (T3) | FC | R11b, R11c | todo |  |
| C52 | §10 A4 | DMA/FPGA need a larger-area defense. Corrected: write–use race exists for every schedule with a gap (T3) | F | R11c | todo |  |
| C53 | §1 "Relation to prior work" | local assurance without a remote verifier. Consequence: time source on the untrusted host; guarantees for ≤ L1 (T4) | FC + R | R11c | todo |  |
| C54 | §1 "Practical stance" | a synthetic time source requires a full timing model (false: replay suffices, P13) | F | R11c | todo |  |
| C55 | §1 "External inputs" | the scheme protects against debugging, thread injection, remote writes (qualified, P12) | F | R11c | todo |  |
| C56 | §5 ¶2 | checksum not collision resistant; protection from dynamic state and timing (made precise by A8 and the forgery theorem) | F | R11c | todo |  |

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
