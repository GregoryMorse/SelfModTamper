# Portable SMC counter probe

`smc_pmc_probe` runs a 27-byte self-modifying loop (a one-byte store, then execution of code near it) and, where the
platform allows, reads the hardware counter for self-modifying-code machine clears around exactly that loop. The
counter is reset and read inside the program, per thread where the OS supports it, so the loader and other processes
do not enter the count. Nothing here is a driver built or signed by this repository.

```
python validation/pmc_test.py            # builds with CMake, runs, saves validation/native/pmc/<time>/
cmake -S validation/pmc -B b && cmake --build b --config Release   # by hand
```

| Platform | Backend | Needs | Status |
|---|---|---|---|
| Linux, Intel or AMD | `perf_event_open`, user mode, per thread | `kernel.perf_event_paranoid <= 2` or root; bare metal (virtual machines usually have no PMU) | written; run on bare metal by the author |
| Windows, AMD | PawnIO (Official, signed), module `AMDFamily17` (allows PerfEvtSel0 and PerfCtr0) | PawnIO installed, administrator prompt | written; untested (no AMD Windows host) |
| Windows, Intel | none: PawnIO's stock `IntelMSR` module denies every PMU MSR | - | timing only |
| macOS x86 | none | - | timing only (the probe builds and runs) |

Even without a counter the timing column separates the cases; that is evidence about one machine, not proof.

Events used (SDM / BKDG primary sources, see `lean/GAPS.md` G20 to G22): Intel `MACHINE_CLEARS.SMC` (C3H, umask 04H);
AMD Family 10h/15h PMCx021. For AMD Zen no pipeline-restart event is verified in this repository: pass `--event`
(for example `0x0461`, the Linux Zen3 table's `l2_request_g2.smc_inval`, an L2 invalidation proxy).

## Getting full coverage

GitHub-hosted runners are virtual machines without a PMU, so CI builds the probe on Linux, Windows and macOS (Intel) and
runs `--selftest` only. Counter data needs bare metal:

- Intel Linux: boot a Linux live USB on an Intel laptop, `sudo sysctl kernel.perf_event_paranoid=2`, run `python3 validation/pmc_test.py`.
- AMD Linux (the author's server): same command; if it is a virtual machine the probe reports it.
- AMD Windows: install PawnIO (Official edition), run the script from an administrator prompt.

Please send the saved `validation/native/pmc/<time>/` folders.
