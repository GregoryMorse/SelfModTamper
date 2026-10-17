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
| Windows, Intel or AMD | Windows' own per-thread hardware-counter profiling (`EnableThreadProfiling`), with `MACHINE_CLEARS.SMC` registered once as a profile source by a WPR `MicroArchitecturalConfig` profile | administrator prompt, Windows 11 build 22453 or later; no driver | written; first Intel run pending (`--register-wpr`, below) |
| Windows, AMD (fallback) | PawnIO (Official, signed), module `AMDFamily17` (allows PerfEvtSel0 and PerfCtr0) | PawnIO installed, administrator prompt | written; untested (no AMD Windows host) |
| macOS x86 | none | - | timing only (the probe builds and runs) |

Even without a counter the timing column separates the cases; that is evidence about one machine, not proof.

Windows, once, from an administrator prompt: `python validation/pmc_test.py --register-wpr` registers the event (it prints
`registered: YES` when `MACHINE_CLEARS.SMC` then appears in the Windows source list); afterwards `python validation/pmc_test.py`
reads it per thread, and the probe prints the thread's context-switch count while counting.

On Windows/Intel the in-process thread-profiling read returned no counter (`HwCountersCount=0`) although the kernel trace shows Windows
counting the registered source per thread, so `python validation/pmc_trace.py` (administrator prompt) takes the counts from a kernel trace:
the probe sleeps 5 ms around each repetition and the script reads the per-thread cumulative counter at those context switches.

Measured so far (evidence about one machine, not proof): AMD EPYC 7542 (Zen2, Linux 5.14, bare metal),
`validation/native/pmc/20261017-linux-amd-epyc7542-zen2/`: with `ic_cache_inval.fill_invalidated` a store into the next
executed instruction gives 2.0 counted invalidations per iteration and stores 64 bytes or more ahead give about 0.0002.
`l2_request_g2.smc_inval` read 0 for this loop.

Events used (SDM / BKDG primary sources, see `lean/GAPS.md` G20 to G22): Intel `MACHINE_CLEARS.SMC` (C3H, umask 04H);
AMD Family 10h/15h PMCx021. For AMD Zen no pipeline-restart event is verified in this repository: the default is `ic_cache_inval.fill_invalidated`
(8Ch/01h, from the Linux Zen tables), an instruction-cache-invalidation proxy; `--event` overrides it.

## Getting full coverage

GitHub-hosted runners are virtual machines without a PMU, so CI builds the probe on Linux, Windows and macOS (Intel) and
runs `--selftest` only. Counter data needs bare metal:

- Intel Linux: boot a Linux live USB on an Intel laptop, `sudo sysctl kernel.perf_event_paranoid=2`, run `python3 validation/pmc_test.py`.
- AMD Linux (the author's server): same command; if it is a virtual machine the probe reports it.
- AMD Windows: install PawnIO (Official edition), run the script from an administrator prompt.

Please send the saved `validation/native/pmc/<time>/` folders.
