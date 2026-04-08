# Tamper-Proofing with Self-Modifying Code

> Polymorphic self-modifying code (SMC) as a runtime integrity mechanism on x86-64 — companion code for the paper and conference presentation by Gregory Morse and Tamás Kozsik.

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

## Requirements

| Requirement | Details |
|---|---|
| OS | Windows 10 / 11 (x64) |
| Compiler | Visual Studio 2019 or later (MSVC + MASM/ml64) |
| Architecture | x86-64 only |
| Privileges | **Administrator** required at runtime (kernel driver for MSR access) |
| External library | [AsmJit](https://github.com/asmjit/asmjit) (JIT assembler, header + library) |
| Kernel driver | [WinRing0 v1.2](http://openlibsys.org/) — `WinRing0x64.sys` (digitally signed) |

> **Note:** The performance-counter features (MSR read/write via `IOCTL_OLS_*`) are accessed through the WinRing0 kernel driver.  Without it the process skips counter setup gracefully but the `MACHINE_CLEARS.SMC` columns will show zero.

## Dependencies

### AsmJit

```bat
REM Clone and build for x64 (adjust generator as needed)
git clone https://github.com/asmjit/asmjit.git D:\libraries\asmjit-master
cd D:\libraries\asmjit-master
cmake -B build_vs2022_x64 -G "Visual Studio 17 2022" -A x64
cmake --build build_vs2022_x64 --config Debug
cmake --build build_vs2022_x64 --config Release
```

By default `PropertySheet.props` expects AsmJit at `D:\libraries\asmjit-master\`.  Update the include and library paths in `SelfModTamper\PropertySheet.props` to match your local checkout, or set the paths via Visual Studio's project property pages.

### WinRing0

Download `WinRing0_1_2_0.zip` from the [WinRing0 release page](http://openlibsys.org/), extract `WinRing0x64.sys`, and place it in the same directory as the compiled executable:

```
x64\Debug\WinRing0x64.sys
x64\Release\WinRing0x64.sys
```

The executable will attempt to register and start the driver as a Windows service on first run and stop/delete it on exit.

## Building

1. Open `SelfModTamper.sln` in Visual Studio.
2. Edit `SelfModTamper\PropertySheet.props` so the AsmJit include and library paths point to your AsmJit build.
3. Select **x64 | Debug** or **x64 | Release** and build.

> Only the **x64** platform is supported.  The static SMC in `TP.asm` uses 64-bit registers and RIP-relative addressing; the dynamic generator in `SelfModTamper.cpp` targets x86-64 exclusively.

> The `.text` section must be writable for the static SMC variants.  This is controlled via the linker flag `/SECTION:.text,RWE` already present in the project.

## Running

```bat
REM Must be run from an elevated (Administrator) command prompt
x64\Release\SelfModTamper.exe
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
├── SelfModTamper.sln          # Visual Studio solution
├── SelfModTamper/
│   ├── SelfModTamper.cpp      # Main source: timer classes, C reference implementations,
│   │                          #   dynamic SMC generator (AsmJit), benchmarking loop
│   ├── TP.asm                 # Static hand-written MASM SMC checksum (TPComp, TPCompLoop)
│   ├── PropertySheet.props    # Shared property sheet — update AsmJit paths here
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

## Citation

If you use this code or reference the paper, please cite:

```bibtex
@unpublished{morse2023tamper,
  author    = {Gregory Morse and Tam{\'a}s Kozsik},
  title     = {Tamper-Proofing with Self-Modifying Code},
  year      = {2023},
  note      = {Manuscript submitted for publication},
  url       = {https://github.com/GregoryMorse/SelfModTamper}
}
```

See also [`CITATION.cff`](CITATION.cff) for the machine-readable citation metadata.

## License

This project is licensed under the MIT License — see [`LICENSE`](LICENSE) for details.

## Authors

- **Gregory Morse** — [gregory.morse@live.com](mailto:gregory.morse@live.com) — Eötvös Loránd University (ELTE), Budapest, Hungary
- **Tamás Kozsik** — [kto@elte.hu](mailto:kto@elte.hu) — Eötvös Loránd University (ELTE), Budapest, Hungary
