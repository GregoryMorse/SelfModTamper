# Tamper-Proofing with Self-Modifying Code

> Polymorphic self-modifying code (SMC) as a runtime integrity mechanism on x86-64 — companion code for the talk presented at **CECC 2022** (Smolenice, Slovakia) and the accompanying dissertation chapter by Gregory Morse and Tamás Kozsik.

## Overview

This repository contains the full experimental implementation described in the paper **"Tamper-Proofing with Self-Modifying Code"**.  The core idea is that SMC executing on a von Neumann architecture introduces timing semantics that cannot be faithfully reproduced by translating the code to an equivalent non-SMC form.  We exploit this property to build a checksum-based tamper-proofing primitive that can detect code modification at runtime.

Key contributions:
- Identification of an x86-64 instruction-encoding pattern that lets SMC swap between `ADC`, `SBB`, `XOR`, and `CMP` by flipping 2 bits, enabling a polymorphic checksum with no conditional branches.
- A static hand-written MASM variant (`TP.asm`) and a fully dynamic variant generated at runtime via [AsmJit](https://asmjit.com/).
- Precise C reference implementations (`TPCompC`, `TPCompCLoop`) that emulate the SMC behavior for correctness validation and performance comparison.
- Timing benchmarks using every available Windows high-resolution timer (RDTSC, RDTSCP, Interrupt Time, Performance Counter, UTC, Tick Count, Multimedia).
- Hardware performance-counter measurement of `MACHINE_CLEARS.SMC` (Intel and AMD; `perf_event_open` on Linux, see `validation/pmc/README.md` for Windows) to quantify pipeline-clear events.

## Paper Abstract

Self-modifying code (SMC) creates unique challenges when it comes to timing semantics on modern hardware for accurate emulation by a maximally efficient non-SMC equivalent.  We investigate the efficacy of using polymorphic SMC to produce a tamper-proofing mechanism that utilises high-accuracy timing measurements which cannot be reproduced by translating the code from the von Neumann architecture to a Harvard architecture.  Our experimental results show that the dynamic SMC variant runs **90× faster** than its non-SMC counterpart while the basic static variant runs **~8× slower** — demonstrating a design space where, with the right unrolling strategy and page-offset selection, SMC achieves smaller size *and* higher performance than any equivalent non-SMC checksum.

## Presentation & Publication Status

This work was presented at:

> Morse, G.; Kozsik, T. **Tamper-Proofing with Self-Modifying Code**. *CECC 2022*, Smolenice, Slovakia, 28 June 2022.

The manuscript is available as the preprint [arXiv:2604.12407](https://arxiv.org/abs/2604.12407) (v1), and forms part of Gregory Morse's doctoral dissertation, which is under review at Eötvös Loránd University (ELTE).

## Requirements

| Requirement | Details |
|---|---|
| OS | Windows 10 / 11, Linux, macOS (all x86-64) |
| Compiler | Windows: Visual Studio 2022 or 2026 (MSVC + MASM/ml64); Linux/macOS: GCC or Clang |
| Architecture | x86-64 only |
| Privileges | none to build or run the program; only reading a hardware counter can need more, see the table below |
| Build system | CMake >= 3.21 (Windows, Linux, macOS x86-64), or the Visual Studio solution (2022 / v143 and 2026 / v145) |
| External library | [AsmJit](https://github.com/asmjit/asmjit), downloaded by the build from a pinned, SHA-512-checked archive (no vcpkg, no manual step) |
| Kernel driver | none. The counter is read with `perf_event_open` on Linux; on Windows see `validation/pmc/README.md` |

### When administrator / root is needed

| What you do | Windows | Linux | macOS |
|---|---|---|---|
| Build (CMake, MSBuild, any script in `validation/` that only compiles) | no | no | no |
| Run `SelfModTamper` / `smc_harness` (timing, checksums, vectors) | **no** (the real-time priority request is silently lowered to high without admin; counter columns read 0) | **no** (counter columns read 0 unless the setting below is made) | **no** (no counter) |
| Counter in the program or the probe, Intel or AMD | not read in-process; use the trace route below | needs `kernel.perf_event_paranoid <= 2` (set once with `sudo sysctl kernel.perf_event_paranoid=2`) or root, and bare metal; the run itself is then unprivileged | not available |
| Counter on Windows through a kernel trace (`python validation/pmc_test.py --register-wpr` once, then `python validation/pmc_trace.py`) | **administrator prompt** | n/a | n/a |
| Windows/AMD fallback through the signed PawnIO driver | **administrator prompt** and PawnIO installed | n/a | n/a |
| Legacy WinRing0 path (not used for results) | administrator prompt and a driver you supply | n/a | n/a |

The scripts check this themselves and say so (`needs an administrator prompt`, or the `perf_event_open failed ... paranoid` line on Linux).

> **Note:** hardware counters are optional. Without one (virtual machines, hosted CI runners, macOS) the `MACHINE_CLEARS.SMC` columns read zero and the timing results are unaffected.

## Dependencies

### AsmJit

All routes (CMake on every platform, the Visual Studio solution, the validation scripts) fetch the same pinned AsmJit archive
(`cmake/asmjit_pin.cmake`: commit, URL and SHA-512) and compile it statically with the program: CMake through `FetchContent`
(`cmake/asmjit.cmake`), the Visual Studio project and the scripts through `cmake -P cmake/fetch_asmjit.cmake` into `build/deps/asmjit`.
Nothing is installed system-wide and no environment variable is needed; the first build needs network access.

### Linux (x86-64)

The benchmark also builds and runs on Linux, with no driver: `cmake -S . -B build && cmake --build build`, then `./build/SelfModTamper`.
`TP.asm` is translated to GNU as by `scripts/masm2gas.py` (so no separate assembler is needed), the Windows calls are replaced by
`SelfModTamper/platform_posix.h`, and `MACHINE_CLEARS.SMC` is read with `perf_event_open` (user mode, this thread; Intel and AMD, needs
`kernel.perf_event_paranoid <= 2` or root and bare metal).  On AMD Zen the counter is the instruction-cache invalidation count
`ic_cache_inval.fill_invalidated`, a proxy, not a pipeline-restart count; set `SMC_EVENT` to use another raw event.  asmjit is fetched and built by CMake from a pinned, SHA-512-checked archive (`cmake/asmjit.cmake`; `-DSMC_WITH_ASMJIT=OFF` skips the dynamic variant); Windows uses the same pin (CMake and the Visual Studio project), so no vcpkg is needed anywhere.  The evidence harness is built as
well: `./build/smc_harness --vectors validation/native/vectors.txt` replays the Lean-generated vectors against the static kernels.
The GNU-as encodings of a few register moves differ from MASM's (same length); the self-modified bytes and the layout the Lean model uses are the same.
Measured so far: `validation/native/runs/linux-amd-epyc7542-zen2/`.

### Portable counter probe (recommended)

`python validation/pmc_test.py` builds `validation/pmc/` with CMake and measures self-modifying-code machine clears around a small
self-modifying loop on Linux (Intel and AMD, via `perf_event_open`, no driver), Windows/AMD (the signed official PawnIO driver and its
signed `AMDFamily17` module) and, timing only, Windows/Intel and macOS.  No driver is built, test-signed or excluded from Defender.
See `validation/pmc/README.md` for coverage and how to get bare-metal runs.  The WinRing0 route below is legacy and is not used for new results.

### Legacy WinRing0 driver

Earlier versions read the counter through the WinRing0 kernel driver. That driver is a known vulnerable driver
(CVE-2020-14979, CVE-2021-41285), no binary of it is kept in the repository, and no result of this work depends on it.  The program
still contains the optional code path that uses it when a `WinRing0x64.sys` is placed next to the executable by the user;
`cmake/winring0/` and `scripts/Build-WinRing0.cmd` build it from source into `build/winring0/` and `validation/winring0_test.py` is the
historic runner.  Use the portable probe above for new measurements.

## Building

Every build product goes under `build/`; the source folders stay clean (`build/msbuild/<toolset>/` for Visual Studio,
`build/cmake-vs2026/`, `build/cmake-vs2022/` or the path you pass for CMake).

### CMake (Windows, Linux, macOS x86-64)

```
cmake -S . -B build/cmake -DCMAKE_BUILD_TYPE=Release
cmake --build build/cmake --config Release
```

or on Windows `cmake --preset windows-x64` then `cmake --build --preset release` (`--preset windows-x64-vs2022` for Visual Studio 2022).
On macOS x86-64 the same CMake build produces the benchmark and the harness without a counter (CI builds and runs it).

### Visual Studio solution

Open `SelfModTamper.sln` (Visual Studio 2022 or 2026, x64 only, Debug or Release), or from a developer prompt:

```
msbuild SelfModTamper.sln /p:Configuration=Release /p:Platform=x64
msbuild SelfModTamper.sln /p:Configuration=Release /p:Platform=x64 /p:PlatformToolset=v143
python validation\native.py --toolset v145     # builds Debug and Release with the matching Visual Studio install
```

The output is `build\msbuild\<toolset>\x64\<Configuration>\SelfModTamper.exe`. AsmJit is downloaded into `build\deps\asmjit` on the first
build. The `.text` section is writable (`/SECTION:.text,RWE`) because the static variants modify their own code; only x64 is supported
(`TP.asm` uses 64-bit registers and RIP-relative addressing).

## Running

```bat
REM from a command prompt; run it from a scratch folder, it writes out.txt and func.asm into the current directory
build\msbuild\v145\x64\Release\SelfModTamper.exe
```

The program:
1. Pins itself to logical processor 0 (Windows, Linux) and asks for real-time priority (Windows; without administrator rights Windows grants high priority instead).
2. Where a counter is available, configures it to count `MACHINE_CLEARS.SMC` events (otherwise those columns read zero).
3. Iterates over five checksum variants × all seven timers for 10 000 trials each.
4. Prints average / min / max times and total `MACHINE_CLEARS.SMC` count per variant.
5. Writes RDTSCP samples for the static SMC variant to `out.txt`.

Sample output (Intel Core i7-9750H, Windows 10):

```
Manufacturer: GenuineIntel
DisplayModel: 0x9E DisplayFamily: 0x6
Architecture Performance Monitoring Version: 4  Number of Performance Counters: 4  PMC bit width: 48
The page size for this system is 4096 bytes.
Code segment base: 0x7FF7B4521000 size: 0x8200
Number of pages: 2  Unrolled loop size per page: 148  Intro bytes: 0x5F  Code size: 0x1B
```

## Project Structure

```
SelfModTamper/
├── CMakeLists.txt             # CMake build (all platforms)
├── CMakePresets.json          # Windows presets
├── cmake/                     # asmjit pin, FetchContent and script-mode fetch, POSIX build, legacy WinRing0 build
├── scripts/                   # masm2gas.py (TP.asm -> GNU as), legacy driver scripts
├── SelfModTamper.sln          # Visual Studio solution (x64; output under build/msbuild)
├── SelfModTamper/
│   ├── SelfModTamper.cpp      # Main source: timer classes, C reference implementations,
│   │                          #   dynamic SMC generator (AsmJit), benchmarking loop
│   ├── TP.asm                 # Static hand-written MASM SMC checksum (TPComp, TPCompLoop)
│   ├── platform_posix.h       # Linux/macOS shim for the Windows calls
│   └── SelfModTamper.vcxproj  # Project file
├── validation/                # Native evidence, counter probe (pmc/), audits
├── lean/                      # The Lean development
├── .gitignore
├── .gitattributes
├── LICENSE
├── CITATION.cff
└── README.md
```

### Checksum variants

| Name | Source | Description |
|---|---|---|
| `C` | `TPCompC` in `.cpp` | Pure C reference — no SMC |
| `SMC` | `TPComp` in `TP.asm` | Static SMC single-loop, modifies its own opcode in-place |
| `C Loop` | `TPCompCLoop` in `.cpp` | Pure C reference emulating loop-unrolled SMC |
| `SMC Loop` | `TPCompLoop` in `TP.asm` | Static loop-unrolled SMC across two 4 KB pages |
| `Dyn SMC Loop` | `gen_asm()` in `.cpp` | Dynamically generated loop-unrolled SMC (AsmJit, RWX heap) |

## Key Results

### Static SMC vs. Non-SMC (220 KB code segment, 10 000 runs)

| Timer | SMC avg | Non-SMC avg | Ratio |
|---|---|---|---|
| RDTSCP (cycles) | 8 305 389 | 1 053 077 | **7.9×** slower |
| Performance Counter | 32 045 | 4 064 | 7.9× slower |

### Dynamic SMC Loop vs. Non-SMC Loop

| Timer | Dyn SMC avg | Non-SMC avg | Ratio |
|---|---|---|---|
| RDTSCP (cycles) | 467 286 | 42 300 840 | **90.5×** faster |
| Performance Counter | 1 803 | 163 204 | 90.6× faster |

### `MACHINE_CLEARS.SMC` events over 10 000 runs

> The program that produced these numbers printed the labels of its last two rows swapped: the row labelled `SMC Loop` measured the dynamic (AsmJit) kernel and the row labelled `Dyn SMC Loop` measured the static `TPCompLoop` (corrected in the current source; the variant table above is the correct mapping). The numbers below are as printed in the paper.

| Variant | Event count |
|---|---|
| C | 4 514 |
| SMC | 83 198 361 |
| C Loop | 20 986 |
| SMC Loop | 4 597 855 |
| Dyn SMC Loop | 4 492 871 |

## Security Notes

The timing-based tamper-proofing scheme rests on several assumptions documented in the paper:

1. A von Neumann (unified instruction/data memory) architecture is in use — not a Harvard architecture.
2. Sufficiently many embedded checksum functions exist that an attacker cannot locate and patch all of them.
3. No non-SMC variant exists that performs as fast or faster on the target hardware.
4. Specialised hardware (e.g. FPGA with direct RAM access) would require a scheme with super-linear area complexity.

The checksum itself is **not** intended to be cryptographically secure in isolation; security of the scheme derives from timing scores and the dynamic/polymorphic nature of the code.

## Instruction Encoding Pattern

The scheme exploits the fact that several classic x86 arithmetic opcodes share an identical encoding except for 2 bits (bits 3–5):

| Instruction | Opcode | Bits [3:5] |
|---|---|---|
| ADD | `0x03` | 0 |
| OR  | `0x0B` | 1 |
| ADC | `0x13` | 2 |
| SBB | `0x1B` | 3 |
| AND | `0x23` | 4 |
| SUB | `0x2B` | 5 |
| XOR | `0x33` | 6 |
| CMP | `0x3B` | 7 |

The SMC checksum cycles between `ADC`, `SBB`, `XOR`, and `CMP` (values 2, 3, 6, 7) by XOR-ing a single byte in the executing instruction stream.

## Lean formalization

The mathematical, algorithmic and quantitative statements of arXiv:2604.12407v1 are formalized in Lean 4 (`lean/`, pinned
`leanprover/lean4:v4.35.0-rc3`, no Mathlib), unconditionally or relative to an explicitly stated platform contract, with corrections
listed in the errata; platform facts are cited and empirical observations are listed as such. This is not a proof of the paper as a
whole: `lean/PAPER_MAP.md` gives every claim, its class and its status, `lean/PLATFORM_CONTRACT.md` lists every hypothesis about the
platform, and `lean/GAPS.md` records what is not proved (notably the abstract intro event count of the unrolled kernel, exact clear counts and the author-side items).

* Selected statement (`lean/SmcTamper/Spec/Paper.lean`): security under the structural assumptions A1-A8 (T1), the mediation cost of
  split views (T2), the necessity of each assumption (T3), the level matrix (T4) and the Harvard separation (C01, C02).
  `lean/Challenge.lean` is generated from the Spec modules; `lean/Solution.lean` proves it. Axioms: `propext`, `Quot.sound`,
  `Classical.choice` only.
* Errata (paper text only) are in `lean/errata/ERRATA.md` and `output/pdf/smctamper-2026-errata.pdf`; fixes to the code, README and
  citation file are in `lean/CODE_FIXES.md`.
* Native tests, assembler listings and timing runs under `validation/native/` are evidence, never proof.
* Build: `python validation/build_modules.py SmcTamper` (memory-capped); CI does the cold build.
* Palomar registration: not yet registered (see `lean/PALOMAR_SUBMISSION.md`).

## Citation

If you use this code or reference the work, please cite the conference presentation:

```bibtex
@misc{morse2022tamper,
  author       = {Gregory Morse and Tam{\'a}s Kozsik},
  title        = {Tamper-Proofing with Self-Modifying Code},
  howpublished = {Presented at CECC 2022, Smolenice, Slovakia},
  month        = jun,
  year         = {2022},
  note         = {Full manuscript unpublished; part of doctoral dissertation under review at E\"{o}tv\"{o}s Lor\'{a}nd University (ELTE)},
  url          = {https://github.com/GregoryMorse/SelfModTamper},
}
```

See also [`CITATION.cff`](CITATION.cff) for the machine-readable citation metadata.

## License

This project is licensed under the MIT License — see [`LICENSE`](LICENSE) for details.

## Authors

- **Gregory Morse** — [gregory.morse@live.com](mailto:gregory.morse@live.com) — Eötvös Loránd University (ELTE), Budapest, Hungary
- **Tamás Kozsik** — [kto@elte.hu](mailto:kto@elte.hu) — Eötvös Loránd University (ELTE), Budapest, Hungary
