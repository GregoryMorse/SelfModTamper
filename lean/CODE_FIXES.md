# Code and docs fixes (not errata)

The repository has no tagged release, so these are not errata (decision of the author, 2026-10-15). They land
before the Palomar commit (R12 unless noted) as minimal diffs; each gets its commit hash here when done.

| ID | File | Defect (found by reading, R1 re-read) | Fix | Test | Status |
|---|---|---|---|---|---|
| L01 | SelfModTamper/SelfModTamper.cpp | `testFuncs` = {C, TPComp, C Loop, TPCompF (dynamic), TPCompLoop (static)} but `strFuncNames` ends {..., "SMC Loop", "Dyn SMC Loop"}: the last two labels are swapped | swap the two names | harness label check | applied in 9b5e125 (R12) |
| L02 | SelfModTamper/SelfModTamper.cpp | the timed interval contains a console write and a driver IOCTL (`getSMCCount`) per run | move both after the end of the timed interval | native run (timing only) | applied in 9b5e125 (R12) |
| L03 | SelfModTamper/SelfModTamper.cpp | `TPCompC` / `TPCompCLoop` dereference `TPComp+1` as an `E9 rel32` incremental-link thunk; with `LinkIncremental=false` (Release) the computed offset is garbage and the emulation silently stops substituting the opcode | follow the thunk only if the first byte is `0xE9` | Release differential vectors | applied in 9b5e125 (R12) |
| L04 | TP.asm, SelfModTamper.cpp | `TPCompLoop` needs `size >= 8` and that 8 divides `size` (otherwise it computes index -1 and patches inside the intro, or reads fewer qwords than the C model) | document and assert the precondition | edge vectors | applied in 9b5e125 (R12) |
| L05 | SelfModTamper.cpp (`gen_asm`) | the intro is measured with placeholder immediates whose sizes differ from the emitted ones; the 95-byte total holds only because the differences cancel (and only if `mov rax, imm` is emitted as 7 bytes) | assert emitted size equals measured size (R5 confirmed the cancellation: `Layout/AsmJitSize.lean`; the assertion guards against an AsmJit version that encodes differently) | harness dump `validation/native_harness.py` | applied in 9b5e125 (R12) |
| L06 | SelfModTamper/TP.asm lines 5 and 50 | `_TEXT$SMC SEGMENT ALIGN(4096)` and its `ENDS` are commented out and enclose `TPComp` only; `TPCompLoop` lies in ordinary `.text`, so the static loop is not page-aligned (the dynamic copy is, via `VirtualAlloc`) | comment only, no change to the assembled bytes (author, 2026-10-15: reconcile without changing behaviour) | listing identical before/after | applied in 9b5e125 (R12) |
| L07 | SelfModTamper/TP.asm, SelfModTamper.cpp (`gen_asm`) | the termination patch (`xor qword ptr [unit+23], rdi`) assumes the byte after the last executed unit's `lea` is 0x48 (the next unit's `adc`); for the last unit of a 148-unit page it is not, so a qword count `n` with `148 | n` makes the patched `jmp` target garbage (access violation). Found natively by `--probe`: n = 148, 296, 592 crash in `TPCompLoop` and the AsmJit kernel; n = 149, 299 and the C emulation do not | guard in `main` (reject `148 | n`) and in the harness; a real fix (REX-padded byte so it is 0x48, or a per-unit constant) is open | `smc_harness --probe 1184 TPCompLoop` crashes, `--probe 1192` passes | guard applied; root-cause fix open (G34) |
| D01 | README.md | "not yet available on arXiv" | cite arXiv:2604.12407; Lean section (R15); Palomar entry and tag added in R16 | - | applied in 9b5e125 (R12) |
| D02 | CITATION.cff | preferred citation | arXiv preprint | optional `cffconvert` | applied in 9b5e125 (R12) |
| D03 | README.md | variant table must agree with L01 | edit | - | applied in 9b5e125 (R12) |

Native evidence runs the product only in the dedicated harness (`validation/native/smc_harness.cpp`, R12); the
product itself needs administrator rights and the WinRing0 driver and is never run by the rounds.

## R12 evidence

* `validation/native/acceptance.json`: Debug and Release harness builds; 36 Lean-generated vectors (`validation/vectors_gen.lean.txt (copy it to a .lean file to run it; the preflight requires every .lean file to be a module)`) pass for `TPComp`, `TPCompC`,
  `TPCompLoop`, `TPCompCLoop` and the AsmJit kernel; the introspective `--text` differential passes; the Release harness built from the pre-fix source fails
  `--text` (L03: C emulations differ from the asm kernels); L07 probes (qword counts 148, 296, 592 crash, 149, 297 do not).
* `validation/data/native_runs.json`, `validation/native/runs/`: unelevated product runs before and after the fixes (counters read zero: no driver). Pattern
  comparison with the paper's Tables 4-5 only; no results are regenerated.
* Build: the Visual Studio 2026 solution (`SelfModTamper.sln`, toolset v145) is authoritative; `CMakePresets.json` now defaults to the `Visual Studio 18 2026`
  generator with a `windows-x64-vs2022` preset (CMake route not exercised here).
* WinRing0 driver (2026-10-17): `scripts/Get-WinRing0.ps1` (a binary download from openlibsys.org, which now redirects and fails) is replaced by
  `cmake/winring0/` + `scripts/Build-WinRing0.cmd`: a git clone of the pinned commit d567440 of the open-source github.com/GermanAizek/WinRing0 (device name `WinRing0_1_2_0` as the
  product expects), kernel-mode headers and libraries from the pinned, hash-checked Microsoft.Windows.WDK.x64 10.0.26100.6584 NuGet package (no WDK installer), compiled with
  cl/link from the installed MSVC tools. Tested here from a clean directory (25 KB `WinRing0x64.sys`, also with `-DWINRING0_TESTSIGN=ON`, which signs with a self-made certificate).
  The result is unsigned: Windows loads it only in test-signing mode, which this machine (Secure Boot, HVCI, driver blocklist) does not have; whether it then loads was not tested.
* Counter measurement (2026-10-17): the WinRing0 route is superseded by `validation/pmc/` + `validation/pmc_test.py`, a portable CMake probe (Linux `perf_event_open` for Intel and AMD, Windows/AMD through the signed official PawnIO driver, timing only elsewhere). WinRing0 1.2.0 is a known vulnerable driver blocked by Windows and Defender; PawnIO's stock IntelMSR module denies the Intel PMU MSRs, so Windows/Intel has no counter. CI builds and self-tests the probe on Linux, Windows and macOS (Intel); hosted runners have no PMU, so counter data comes from bare-metal runs.
* Linux port (2026-10-17): `CMakeLists.txt` + `cmake/posix.cmake`, `SelfModTamper/platform_posix.h`, `scripts/masm2gas.py`; `SelfModTamper.cpp` and `validation/native/smc_harness.cpp` gain `#ifdef _WIN32` guards only (the Windows build is unchanged). The static kernels are assembled by GNU as from a translation of TP.asm (TPCompLoop is 8123 bytes as in the Lean layout; GAS and MASM pick different, same-length encodings for some register-register moves). On an AMD EPYC 7542 (Linux) all 36 Lean-generated vectors agree for TPComp, TPCompC, TPCompLoop and TPCompCLoop and the introspective `--text` run agrees. asmjit is now fetched by CMake (`cmake/asmjit.cmake`, pinned commit 9eb6edb and its SHA-512, the same as the vcpkg baseline) on Linux and in the Windows CMake route; on the AMD EPYC all five kernels including the asmjit one agree on the 36 vectors.
