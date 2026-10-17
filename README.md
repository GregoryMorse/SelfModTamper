# Tamper-Proofing with Self-Modifying Code

> Polymorphic self-modifying code (SMC) as a runtime integrity mechanism on x86-64 — companion code for the talk presented at **CECC 2022** (Smolenice, Slovakia) and the accompanying dissertation chapter by Gregory Morse and Tamás Kozsik.

## Overview

This repository contains the full experimental implementation described in the paper **"Tamper-Proofing with Self-Modifying Code"**.  The core idea is that SMC executing on a von Neumann architecture introduces timing semantics that cannot be faithfully reproduced by translating the code to an equivalent non-SMC form.  We exploit this property to build a checksum-based tamper-proofing primitive that can detect code modification at runtime.

Key contributions:
- Identification of an x86-64 instruction-encoding pattern that lets SMC swap between `ADC`, `SBB`, `XOR`, and `CMP` by flipping 2 bits, enabling a polymorphic checksum with no conditional branches.
- A static hand-written MASM variant (`TP.asm`) and a fully dynamic variant generated at runtime via [AsmJit](https://asmjit.com/).
- Precise C reference implementations (`TPCompC`, `TPCompCLoop`) that emulate the SMC behavior for correctness validation and performance comparison.
- Timing benchmarks using every available Windows high-resolution timer (RDTSC, RDTSCP, Interrupt Time, Performance Counter, UTC, Tick Count, Multimedia).
- Hardware performance-counter measurement of `MACHINE_CLEARS.SMC` (Intel) via the WinRing0 kernel driver to quantify pipeline-clear events.

## Paper Abstract

Self-modifying code (SMC) creates unique challenges when it comes to timing semantics on modern hardware for accurate emulation by a maximally efficient non-SMC equivalent.  We investigate the efficacy of using polymorphic SMC to produce a tamper-proofing mechanism that utilises high-accuracy timing measurements which cannot be reproduced by translating the code from the von Neumann architecture to a Harvard architecture.  Our experimental results show that the dynamic SMC variant runs **90× faster** than its non-SMC counterpart while the basic static variant runs **~8× slower** — demonstrating a design space where, with the right unrolling strategy and page-offset selection, SMC achieves smaller size *and* higher performance than any equivalent non-SMC checksum.

## Presentation & Publication Status

This work was presented at:

> Morse, G.; Kozsik, T. **Tamper-Proofing with Self-Modifying Code**. *CECC 2022*, Smolenice, Slovakia, 28 June 2022.

The manuscript is available as the preprint [arXiv:2604.12407](https://arxiv.org/abs/2604.12407) (v1), and forms part of Gregory Morse's doctoral dissertation, which is under review at Eötvös Loránd University (ELTE).

## Requirements

| Requirement | Details |
|---|---|
| OS | Windows 10 / 11 (x64) |
| Compiler | Visual Studio 2019 or later (MSVC + MASM/ml64) |
| Architecture | x86-64 only |
| Privileges | **Administrator** required at runtime (kernel driver for MSR access) |
| Build system | CMake ≥ 3.21 + [vcpkg](https://vcpkg.io/) (recommended) **or** `.vcxproj` directly |
| External library | [AsmJit](https://github.com/asmjit/asmjit) — auto-resolved by vcpkg, or manual build |
| Kernel driver | [WinRing0](https://github.com/GermanAizek/WinRing0) built from a pinned commit — `WinRing0x64.sys` (unsigned; see below) |

> **Note:** The performance-counter features (MSR read/write via `IOCTL_OLS_*`) are accessed through the WinRing0 kernel driver.  Without it the process skips counter setup gracefully but the `MACHINE_CLEARS.SMC` columns will show zero.

## Dependencies

### AsmJit

**Recommended — vcpkg (automatic):** `vcpkg.json` already declares the `asmjit` dependency.
When you configure with CMake (see [Building](#building)), vcpkg installs AsmJit into
`vcpkg_installed/` automatically — no separate clone or build step is needed.

**Alternative — manual build with `ASMJIT_DIR`:** If you prefer to build AsmJit yourself
and use the `.vcxproj` directly without vcpkg, set the `ASMJIT_DIR` environment variable to
the root of your AsmJit checkout (the directory containing the `src` subfolder), then build:

```bat
git clone https://github.com/asmjit/asmjit.git C:\path\to\asmjit
cd C:\path\to\asmjit
cmake -B build_vs2022_x64 -G "Visual Studio 17 2022" -A x64
cmake --build build_vs2022_x64 --config Debug
cmake --build build_vs2022_x64 --config Release
```

```powershell
# Set ASMJIT_DIR permanently for your user account
[System.Environment]::SetEnvironmentVariable("ASMJIT_DIR", "C:\path\to\asmjit", "User")
```

`SelfModTamper\PropertySheet.props` reads `$(ASMJIT_DIR)` automatically; no manual editing
of the property sheet is required.

### Portable counter probe (recommended)

`python validation/pmc_test.py` builds `validation/pmc/` with CMake and measures self-modifying-code machine clears around a small
self-modifying loop on Linux (Intel and AMD, via `perf_event_open`, no driver), Windows/AMD (the signed official PawnIO driver and its
signed `AMDFamily17` module) and, timing only, Windows/Intel and macOS.  No driver is built, test-signed or excluded from Defender.
See `validation/pmc/README.md` for coverage and how to get bare-metal runs.  The WinRing0 route below is legacy and is not used for new results.

### WinRing0

The kernel driver `WinRing0x64.sys` is required to read hardware performance counters (`MACHINE_CLEARS.SMC`).
Without it the benchmark still runs but counter columns show zero.

No binary of the driver is downloaded.  `cmake/winring0/` clones a pinned commit of the open-source
[GermanAizek/WinRing0](https://github.com/GermanAizek/WinRing0) repository (a maintained fork of the OpenLibSys WinRing0 1.2
sources; same device name `WinRing0_1_2_0`), takes the kernel-mode headers and libraries from Microsoft's pinned
`Microsoft.Windows.WDK.x64` NuGet package (SHA-256 checked; no WDK installer, no administrator rights) and compiles it with the
MSVC tools of Visual Studio / Build Tools:

```bat
scripts\Build-WinRing0.cmd
```

It writes `WinRing0x64.sys` into the repository root (excluded from version control) and CMake copies it next to the executable.
`python validation\winring0_test.py` runs this automatically when the file is missing.

**The source build is unsigned.**  Windows loads kernel drivers only when they are signed, so on a machine with Secure Boot, Memory
integrity (HVCI) or the vulnerable-driver blocklist an unsigned build does not load and the counters read zero (`-DWINRING0_TESTSIGN=ON`
test-signs it, which Windows accepts only in test-signing mode).

**Measurement runs use the signed 1.2.0 driver instead** (`python validation\winring0_test.py`, option `--driver signed`, the default): the
file committed to the xmrig repository is downloaded from a pinned commit and checked against its git blob id before it is written.
WinRing0 1.2.0 is a **known vulnerable driver** (CVE-2020-14979, CVE-2021-41285) on Microsoft's blocklist, so the runner stops and deletes its
service after each run, and again at the end, also when a run fails, and removes its copies.  Defender may delete the file on download;
`--defender-exclusion` excludes only the download directory for the duration of the run.  Use `--driver build` for the source build.

The executable registers and starts the driver as a Windows service on each run and
stops/deletes it cleanly on exit.

## Building

### Prerequisites

| Tool | How to get |
|---|---|
| Visual Studio 2019+ | [visualstudio.microsoft.com](https://visualstudio.microsoft.com/) — Desktop Development with C++ workload |
| CMake ≥ 3.21 | Bundled with Visual Studio, or [cmake.org](https://cmake.org/download/) |
| vcpkg | [github.com/microsoft/vcpkg](https://github.com/microsoft/vcpkg) — clone and set `VCPKG_ROOT` |

Set `VCPKG_ROOT` permanently if you have not already:

```powershell
[System.Environment]::SetEnvironmentVariable("VCPKG_ROOT", "C:\path\to\vcpkg", "User")
```

---

### Option A — CMake + vcpkg (recommended)

AsmJit is installed automatically from `vcpkg.json`.

```bat
REM 1. Build the WinRing0 driver from source (one-time setup, needs the WDK)
scripts\Build-WinRing0.cmd

REM 2. Configure (installs AsmJit via vcpkg, generates Visual Studio project files in build\)
cmake --preset windows-x64

REM 3. Build
cmake --build --preset release
REM  or for Debug:
cmake --build --preset debug
```

Output: `build\Release\SelfModTamper.exe` / `build\Debug\SelfModTamper.exe`

> The default preset uses the **Visual Studio 18 2026** generator; use `--preset windows-x64-vs2022` for Visual Studio 2022. The
> Visual Studio solution (`SelfModTamper.sln`) is the authoritative build; CMake is the secondary route.

---

### Option B — Visual Studio IDE (Open Folder)

Visual Studio 2022 and later detect `CMakeLists.txt` and `CMakePresets.json` when you use
**File → Open → Folder**.

1. Run `scripts\Build-WinRing0.cmd` once (see above).
2. **File → Open → Folder** — select the repository root.
3. Visual Studio configures CMake and restores vcpkg packages automatically.
4. Select the **x64-Release** or **x64-Debug** target and build.

> Ensure `VCPKG_ROOT` is set in your user environment *before* opening Visual Studio.

---

### Option C — Visual Studio `.vcxproj` (legacy)

The original `SelfModTamper.sln` / `.vcxproj` remain for users who prefer the MSBuild
workflow.  AsmJit paths are resolved via `PropertySheet.props`.

**Providing AsmJit via vcpkg (required):**

Either run `vcpkg integrate install` once (applies vcpkg to all VS projects on this machine):

```bat
vcpkg integrate install
```

Or set `VCPKG_ROOT` and restart Visual Studio — `Directory.Build.props` and `PropertySheet.props`
automatically bridge it to MSBuild, install packages from `vcpkg.json`, and copy `asmjit.dll` to the output.

Run `scripts\Build-WinRing0.cmd` once to build and place `WinRing0x64.sys` in the repository root (the
build copies it next to the executable automatically).  Then open `SelfModTamper.sln`, select
**x64 | Debug** or **x64 | Release**, and build.

**Using a manual AsmJit build (without vcpkg):**

Set `ASMJIT_DIR` as described in [Dependencies → AsmJit](#asmjit) and restart Visual Studio.
`PropertySheet.props` picks up the variable automatically.

> Only the **x64** platform is supported.  The static SMC in `TP.asm` uses 64-bit registers
> and RIP-relative addressing; the dynamic generator in `SelfModTamper.cpp` targets x86-64
> exclusively.
>
> The `.text` section must be writable for the static SMC variants.  This is controlled via
> the linker flag `/SECTION:.text,RWE` already present in the project.

## Running

```bat
REM Must be run from an elevated (Administrator) command prompt
REM CMake build output:    build\Release\SelfModTamper.exe
REM .vcxproj build output: x64\Release\SelfModTamper.exe
build\Release\SelfModTamper.exe
```

The program:
1. Pins itself to logical processor 0 and raises its priority to real-time.
2. Loads/starts the WinRing0 driver and configures `IA32_PERFEVTSEL0` to count `MACHINE_CLEARS.SMC` events.
3. Iterates over five checksum variants × all seven timers for 10 000 trials each.
4. Prints average / min / max times and total `MACHINE_CLEARS.SMC` count per variant.
5. Writes RDTSCP samples for the static SMC variant to `out.txt`.
6. Unloads the driver cleanly on exit.

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
├── CMakeLists.txt             # Primary CMake build (recommended)
├── CMakePresets.json          # Build presets — windows-x64 (Release/Debug)
├── vcpkg.json                 # vcpkg manifest — declares AsmJit dependency
├── scripts/
│   └── Build-WinRing0.cmd     # Builds WinRing0x64.sys from source (cmake/winring0)
├── SelfModTamper.sln          # Visual Studio solution (legacy .vcxproj build)
├── SelfModTamper/
│   ├── SelfModTamper.cpp      # Main source: timer classes, C reference implementations,
│   │                          #   dynamic SMC generator (AsmJit), benchmarking loop
│   ├── TP.asm                 # Static hand-written MASM SMC checksum (TPComp, TPCompLoop)
│   ├── Directory.Build.props  # MSBuild early hook — sets VcpkgManifestRoot before vcpkg.props runs
│   ├── PropertySheet.props    # MSBuild property sheet — bridges VCPKG_ROOT; Option C ASMJIT_DIR
│   └── SelfModTamper.vcxproj  # Project file
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
