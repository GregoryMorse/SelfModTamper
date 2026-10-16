# Errata and model clarifications — Tamper-Proofing with Self-Modifying Code

Against arXiv:2604.12407v1. Generated from `edits.json` by `validation/make_errata.py`.

## P01 — Section 7, display after "back-of-the-envelope estimate" (p. 8; Lean; certain)

**Before:**

```tex
\frac{10{,}000 \cdot (467{,}286 - 414{,}188)}{2{,}158{,}056} \approx 246,
\qquad
\frac{246}{10{,}000} \approx 2.5\%,
```

**After:**

```tex
\frac{10{,}000 \cdot (467{,}286 - 414{,}188)}{2{,}158{,}056 - 414{,}188} \approx 304,
\qquad
\frac{304}{10{,}000} \approx 3.0\%,
```

**Reason:** The estimate must divide by max - min: if an undisturbed run takes the minimum and a disturbed one the maximum, the disturbed fraction is (avg - min)/(max - min), not (avg - min)/max.

**Evidence:** Arithmetic on Table 5 (RDTSCP, SMC columns): 10000*(467286-414188)/(2158056-414188) = 304.48; the printed formula gives 246.05. Lean: Data.Estimator (R10).

**Source:** Table 5; Section 7

## P01.2 — Section 7, sentence after the display (p. 8; Lean; certain)

**Before:**

```tex
gives roughly $3.6\%$.
```

**After:**

```tex
gives roughly $7.8\%$ (Table~\ref{tbl:dynresult}, non-SMC columns, with the minimum subtracted in the same way).
```

**Reason:** Same correction as P01 for the non-SMC columns: (42,300,840 - 39,600,010)/(74,295,022 - 39,600,010) = 7.78%, whereas 3.6% divides by the maximum.

**Evidence:** Arithmetic on Table 5 (RDTSCP, non-SMC columns). Lean: Data.Estimator (R10).

**Source:** Table 5; Section 7

## P02 — Section 7, paragraph introducing Table 5 (p. 8; Lean; certain)

**Before:**

```tex
about $2.5\times$
faster than the static SMC implementation
```

**After:**

```tex
about $17.8\times$
faster than the basic static SMC implementation (Table~\ref{tbl:staticresult})
```

**Reason:** Table 4 over Table 5 gives 8,305,389/467,286 = 17.8 (RDTSCP averages); no ratio of the tables' entries is 2.5.

**Evidence:** Arithmetic on Tables 4 and 5 (RDTSCP, SMC columns): 17.77; minima 7,466,412/414,188 = 18.03; the only ratio near 2.5 is basic C over dynamic SMC, 1,053,077/467,286 = 2.25 (Table 4 non-SMC over Table 5 SMC), which the sentence does not describe. Lean: Data.Ratios (R10).

**Source:** Tables 4 and 5; Section 7

## P03 — Caption of Table 4 (p. 9; editorial; inferred)

**Before:**

```tex
the checksum covered the entire 220~KB code segment.
```

**After:**

```tex
the checksum covered the entire 32.5~KiB (0x8200-byte) code segment.
```

**Reason:** Figure 5 prints a code-segment size of 0x8200 bytes, and the clear count in Table 6 equals two clears per 8-byte word of exactly that region.

**Evidence:** Figure 5: "size: 0x8200 End address: 0x7FF7B4529200" with base 0x7FF7B4521000. Table 6: 83,198,361 clears / 10,000 runs = 8,319.84 per run = 1.99996 per 8-byte word of 0x8200 bytes (4,160 words); for 220 KB it would be 0.295 per word. Inferred because the author may have measured a different build than the one in Figure 5.

**Source:** Figure 5; Table 6

## P04 — Section 1, paragraph "Model" (p. 2; Lean; certain)

**Before:**

```tex
returns true if and only if the
protected code remains unmodified.
```

**After:**

```tex
returns true for the unmodified protected code (when its timing lies within the calibrated bounds) and false for every modification that changes the checksum state or violates the time bound.
```

**Reason:** A checksum is not injective, so "if and only if" is false; the provable statement is completeness for the genuine code and detection of every modification that changes the checksum state or violates the time bound.

**Evidence:** Lean: Detection.Collision (R11a) exhibits two different images with equal kernel output (collision witness); Detection.Predicate states completeness and conditional soundness.

**Source:** Sections 1 and 9

## P04.2 — Section 9, first paragraph (p. 10; Lean; certain)

**Before:**

```tex
returns true if and only if the protected code has not been modified.
```

**After:**

```tex
returns true for the unmodified protected code (when its timing lies within the calibrated bounds) and false for every modification that changes the checksum state or violates the time bound.
```

**Reason:** Same as P04.

**Evidence:** As P04.

**Source:** Section 9

## P05 — Table 6, row labels (p. 10; listing; inferred)

**Before:**

```tex
SMC Loop & 4597855 \\ \hline
Dyn SMC Loop & 4492871 \\ \hline
```

**After:**

```tex
SMC Loop & 4492871 \\ \hline
Dyn SMC Loop & 4597855 \\ \hline
```

**Reason:** In the measurement program the label "SMC Loop" was printed for the dynamically generated kernel and "Dyn SMC Loop" for the statically assembled one, so the counts under the two labels belong to the other variant.

**Evidence:** SelfModTamper.cpp: testFuncs index 3 is TPCompF (dynamic) and index 4 is TPCompLoop (static), while strFuncNames[3] = "SMC Loop" and strFuncNames[4] = "Dyn SMC Loop". The author confirmed (2026-10-15) that the 2022 measurements were taken with this code, so the published row labels are swapped. Inferred only in that the table was transcribed from the program output with its labels.

**Source:** Table 6; SelfModTamper.cpp

## P05.2 — Section 7, first paragraph (p. 8; listing; inferred)

**Before:**

```tex
stable for fine-grained timing.
```

**After:**

```tex
stable for fine-grained timing.  Each timed interval also contained one console write and one performance-counter driver call, which add the same kind of overhead to every variant.
```

**Reason:** The measured intervals were not limited to the kernel; the reader needs to know what else they contained.

**Evidence:** SelfModTamper.cpp lines 697-703: std::cout and getSMCCount (IOCTL) run between the start and end of the timer. The author confirmed (2026-10-15) that the 2022 measurements used this code.

**Source:** Tables 4-6; SelfModTamper.cpp

## P06 — Caption of Figure 3 (p. 7; Lean; certain)

**Before:**

```tex
The three arguments are the start address \lstinline|pData|, the protected length \lstinline|ulSize|, and the function start address \lstinline|pTPCompOffset|; \lstinline|sum| stores the checksum result.
```

**After:**

```tex
The function arguments are the start address \lstinline|pData|, the protected length \lstinline|ulSize| (a multiple of 8 bytes) and the result address \lstinline|pResult|; \lstinline|pTPCompOffset| is the address of the body of the kernel \lstinline|TPComp| and is computed before the loop (not shown), \lstinline|sum| is stored to \lstinline|*pResult|, and \lstinline|op| is the persistent opcode state. The emulation is exact for an 8-byte-aligned region when \lstinline|op| equals the opcode state of the kernel at entry.
```

**Reason:** The caption lists pTPCompOffset as an argument and omits pResult; the figure also relies on an alignment/length precondition and on the opcode state persisting between calls.

**Evidence:** SelfModTamper.cpp TPCompC(PULONG64 pData, ULONG64 ulSize, PULONG64 pResult) computes pTPCompOffset before the loop and declares op as static; Lean: Static.Emulation (R4) states the precondition.

**Source:** Figure 3; SelfModTamper.cpp lines 417-439

## P07 — Table 2, CMP row, LAT column (p. 6; editorial; inferred)

**Before:**

```tex
CMP & 0x3B & 7 & 0.2 / 0.25
```

**After:**

```tex
CMP & 0x3B & 7 & 1
```

**Reason:** A latency of 0.2-0.25 cycles is not a possible latency (the number is a reciprocal throughput); the measured register-to-flags latency of CMP is 1 cycle.

**Evidence:** uops.info (measured) CMP (R64, M64): latency operand 1 -> flags = 1 on Skylake and Zen 3. The cited AsmGrid page is an interactive table that could not be read here, so the reciprocal-throughput cells are not changed. The author chose this correction (2026-10-15).

**Source:** Table 2; https://uops.info/html-lat/SKL/CMP_R64_M64-Measurements.html

## P08 — Section 1, paragraph "Model" (p. 2; Lean; certain)

**Before:**

```tex
constant-time algorithmic kernels
```

**After:**

```tex
algorithmic kernels whose control flow and instruction count are independent of the data
```

**Reason:** The kernels execute a data-independent instruction sequence, but individual instructions still differ in cost (Table 2), so "constant-time" overstates the property.

**Evidence:** Lean: Static.ConstantFlow and Unrolled.Level1 (control flow and instruction count independent of the data, R4/R6).

**Source:** Section 1; Table 2

## P09 — Section 8, first paragraph (p. 9; Lean; certain)

**Before:**

```tex
$c_{\text{non-SMC}}\,\mathcal{O}(n) \gg c_{\text{SMC}}\,\mathcal{O}(n)$
```

**After:**

```tex
$c_{\text{non-SMC}}\,n \gg c_{\text{SMC}}\,n$
```

**Reason:** An asymptotic class absorbs constants, so a comparison of the two constants cannot be written with O(n) on both sides.

**Evidence:** Measured cycles per 8-byte word (Tables 4-6): about 10,168 (C Loop) versus 112 (dynamic SMC). Lean: Data.Ratios (R10).

**Source:** Section 8; Tables 4-5

## P10 — Table 3 (p. 6; editorial; certain)

**Before:**

```tex
SHL & Shift left (unsigned)
```

**After:**

```tex
SHL & Shift left (logical, same as SAL)
```

**Reason:** SHL is the logical shift; "unsigned" is not the architectural name.

**Evidence:** Intel SDM Vol. 2B, SAL/SAR/SHL/SHR.

**Source:** Table 3

## P11 — Section 10 (Security assumptions and threat model), whole section (p. 10; Lean; certain)

**Before:**

```tex
\section{Security assumptions and threat model}\label{sec:assumptions}

The scope of the model is defined by four main assumptions.
\begin{enumerate}
  \item A von Neumann architecture is available; pure Harvard architectures fall
  outside the intended deployment model.
  \item An attacker cannot discover and neutralize all embedded checksum
  functions.
  \item There does not exist a semantics-faithful non-SMC implementation that is
  as fast as, or faster than, the SMC version under the same timing constraints.
  \item Specialized hardware with direct memory access, such as certain FPGA-based
  platforms, would require a correspondingly larger-area defense strategy.
\end{enumerate}

These assumptions intentionally separate what is being claimed from what is not.
For example, self-reconfigurable hardware effectively realizes SMC in another
substrate and is therefore compatible with the model rather than excluded by it.
Similarly, the mechanism is not claimed to be equivalent to cryptographic
attestation; it is a local runtime-integrity technique intended to raise attacker
cost substantially on commodity systems.
```

**After:**

```tex
\section{Security assumptions and threat model}\label{sec:assumptions}

We state the adversary, its goal, the assumptions the scheme needs, and what is proved.  The statements are formalised and checked in Lean (Section~\ref{sec:summary}); platform behaviour enters only as explicit contract fields (timing bounds, which capabilities a privilege level has), not as proved facts about hardware.

\paragraph{Adversary levels.}
L0: patches the protected bytes before execution.
L1: user mode; may write to the protected process while it runs, single-step or breakpoint it, run it under emulation, and hook operating-system timer interfaces.
L2: kernel or hypervisor; additionally may give instruction fetch and data reads different views of memory and may trap or offset the time-stamp counter.
L4: additionally has physical writers such as DMA devices.
(L3 is reserved and has the capabilities of L2 in the model.)
The \emph{goal} is that a protected byte other than a legitimately varying SMC opcode byte is executed in modified form while no alarm is effective.
An alarm is effective when a checksum unit whose own response code is unmodified sees a wrong result, or $k$ consecutive checks of one unit exceed its time threshold $\tau$.

\paragraph{Assumptions.}
A1 (coherence, replaces ``von Neumann architecture''): the fetch and data views are one image.
A2 (coverage, replaces ``cannot neutralize all functions''): every protected byte lies in the region of some checksum unit, each unit's own code is protected, the coverage graph of the units (a unit covers another when its region contains the other's code) is strongly connected, and at least one unit is never modified.
A3 (timing gap, replaces the non-existence of an equally fast non-SMC implementation): the native check time is at most $\tau$, and $\tau$ is below the lower bounds on emulation, on a debug trap, and on mirroring an opcode write.
A4 (no physical writer): no device other than the protected thread writes the protected memory; a larger-area defense narrows the window between check and use but cannot close it.
A5 (time integrity): every timer reading equals the elapsed time.
A6 (persistence): a modification persists through the next $k$ scheduled checks of each unit that covers it.
A7 (response coverage): each unit's alarm response code is part of its own protected code.
A8 (non-compensation): a modification inside the region of a running unit changes the unit's result.
The checksum is deliberately not collision resistant, so A8 is an assumption about the design, and it cannot be dropped: two modified quadwords can restore the final sum and opcode state.

\paragraph{Results.}
(T1) Under A1--A8 and the platform contract, no adversary achieves the goal.
(T2) With separate fetch and data views, a run that follows the SMC kernel's opcode trajectory needs one mirroring event per opcode-changing iteration, each costing at least the mirroring bound of A3; a plain checksum without opcode state can be blind to split views.
(T3) Each of A1, A2 (coverage and one unmodified unit), A3, A4, A5, A6 and A8 is necessary: for each there is a system and an adversary that satisfies all the others and wins.
(T4) With the inline time-stamp counter, levels L0 and L1 satisfy A1, A4 and A5; an operating-system timer interface can be hooked at L1; L2 breaks A1 and A5; L4 breaks A4.
With a time source outside the adversary's control, of resolution $r$ and jitter $j$, slowdowns of at least $j+2r$ are detected by a threshold calibrated on native runs.

\paragraph{Scope.}
Not claimed: protection against code injected outside the checksummed bytes, against register tampering outside timed intervals, or against a modification that is undone before the next covering check; guarantees against L2 and above without an external clock; equivalence to cryptographic attestation.
The mechanism is a local runtime-integrity technique intended to raise attacker cost on commodity systems, and the proofs cover the model above, not the hardware.
```

**Reason:** The section states no adversary capabilities, goal or security statement; assumption 3 is an uncheckable universal negative, assumption 4 a remark, and assumptions the scheme needs (time integrity, persistence, response coverage, non-compensation) are missing.

**Evidence:** Lean: Threat.Security (T1), Threat.T3 (T3), Threat.SplitMirror (T2), Threat.Matrix (T4); consistency Threat.Witness; scope Threat.Scope.

**Source:** Section 10; plan D11

**Lean:** `SmcTamper.security`, `SmcTamper.witness_secure`, `SmcTamper.faithful_needs_med`, `SmcTamper.mediated_timefail`, `SmcTamper.T3`, `SmcTamper.T4`, `SmcTamper.tsc_low_level`, `SmcTamper.ext_clock_detects`, `SmcTamper.injected_code_outside_goal`

## P12 — Section 1, paragraph "External inputs" (p. 2; Lean; certain)

**Before:**

```tex
moreover, such channels do not protect code at the machine-architecture level
against manual debugging, thread injection, or remote process-memory writes.
```

**After:**

```tex
moreover, such channels do not protect code at the machine-architecture level
against manual debugging, thread injection, or remote process-memory writes.  The mechanism proposed here does not prevent these either: it detects persistent modification of the checksummed bytes and interference inside timed intervals, but not injected code that leaves the checksummed bytes intact, register tampering outside timed intervals, or a modification that is undone before the next covering check (Section~\ref{sec:assumptions}).
```

**Reason:** The sentence suggests that the proposed scheme protects against debugging, thread injection and remote memory writes; it does not.

**Evidence:** Lean: Threat.Scope (injected_code_outside_goal, noeffect_events), Threat.T3 (necessary_A6: write-execute-restore between checks wins).

**Source:** Section 1

**Lean:** `SmcTamper.injected_code_outside_goal`, `SmcTamper.noeffect_events`, `SmcTamper.necessary_A6`

## P13 — Section 1, paragraph "Practical stance" (p. 2; Lean; certain)

**Before:**

```tex
An attacker could
attempt to simulate execution under a synthetic time source and adapt the
predicate accordingly, but this requires a deterministic, fully characterizable
timing model.  Modern commodity processors do not satisfy this assumption.
```

**After:**

```tex
An attacker who controls the time source need not model the processor at all: replaying readings recorded from native runs makes any threshold predicate on those readings pass.  Timing-based detection therefore requires a time source outside the adversary's control, for example \texttt{RDTSC}/\texttt{RDTSCP} read inside the protected code against a user-mode adversary, or an external source against a kernel-level adversary.  An adversary who must run the protected code under emulation with an honest clock needs a deterministic, fully characterizable timing model, and modern commodity processors do not admit one.
```

**Reason:** Replaying recorded timer readings defeats any timing predicate when the adversary controls the clock, so a synthetic time source needs no timing model.

**Evidence:** Lean: Threat.Witnesses (nec_A5: a replayed native reading passes while a slow emulation runs), Threat.Matrix (nec_A5_osApi, T4, ext_clock_detects).

**Source:** Section 1; plan D11

**Lean:** `SmcTamper.necessary_A5`, `SmcTamper.nec_A5_osApi`, `SmcTamper.T4`, `SmcTamper.ext_clock_detects`

## P14 — Table 1, AMD64 column (counter global control MSR and SMC event) (p. 5; editorial, open; inferred)

**Before:**

```tex
Perf. Counter Global Control & 0x38F & 0xC0000301
```

**After:**

```tex
(pending research: cite the AMD document that defines MSR C000_0301 and PMCx021 for the microarchitectures covered, or correct the cells)
```

**Reason:** The AMD cells have no primary source in the paper's references that was found: the 2012 copy of the AMD64 APM Vol. 2 (rev 3.21) confirms MSRs C001_0000 (PerfEvtSel0) and C001_0004 (PerfCtr0) but contains neither C000_0301 nor event 0x21.

**Evidence:** Searched: AMD64 APM Vol. 2 rev 3.21 (March 2012; the author's OneDrive copy; the paper cites the January 2023 revision, not available here); Linux perf JSON for amdzen1-5 (no self-modifying-code event); AMD BKDG/PPR downloads failed. Intel column verified (Linux perf skylake pipeline.json: C3H/04H MACHINE_CLEARS.SMC). To be settled by the author supplying the AMD revision or by research in a later session.

**Source:** Table 1; AMD APM Vol. 2

