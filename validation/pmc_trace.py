"""Windows (administrator prompt): measure MACHINE_CLEARS.SMC around each repetition of the probe's loop from a kernel trace.

    python validation/pmc_trace.py                 # needs: python validation/pmc_test.py --register-wpr (once)

Windows keeps a per-thread cumulative counter and writes it into the trace at every context switch of the thread.  The probe
(--trace-markers) brackets every repetition with a 5 ms sleep, so the trace holds the counter value just before and just after
each repetition; the count of a repetition is the difference.  Kernel code is not counted (the profile source is user mode only
as far as the Windows source definition goes; this is not checked here).  The numbers are evidence about this machine, never proof.
"""
import argparse
import ctypes
import json
import re
import statistics
import subprocess
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import pmc_test  # noqa: E402

XPERF = r"C:\Program Files (x86)\Windows Kits\10\Windows Performance Toolkit\xperf.exe"
CASES = [
    "store into the next executed instruction (+0)",
    "store 64 bytes ahead, same page",
    "store 1024 bytes ahead, same page",
    "store at the start of the next page",
    "store two pages ahead",
]


def pmc_events(dumper, tid):
    rows = []
    pat = re.compile(r"^\s+Pmc,\s+(\d+),\s+(\d+),\s+(\d+)")
    with open(dumper, encoding="utf-8", errors="replace") as f:
        for line in f:
            if line.lstrip().startswith("Pmc,"):
                m = pat.match(line)
                if m and int(m.group(2)) == tid:
                    rows.append((int(m.group(1)), int(m.group(3))))
    rows.sort()
    return rows


def analyze(rows, ncases, reps):
    """Markers: two consecutive events at least 3 ms apart whose counter values are (almost) equal, i.e. the thread slept."""
    marks = []
    for (t0, v0), (t1, v1) in zip(rows, rows[1:]):
        if t1 - t0 >= 3000 and abs(v1 - v0) <= 64:
            marks.append((v0, v1))  # value when the thread left the CPU, value when it came back
    need = 2 * ncases * reps
    if len(marks) < need:
        return None, "found %d sleep markers, expected %d" % (len(marks), need)
    marks = marks[-need:]
    counts = [marks[2 * i + 1][0] - marks[2 * i][1] for i in range(ncases * reps)]  # leave(post) - return(pre)
    return [counts[c * reps:(c + 1) * reps] for c in range(ncases)], ""


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--iters", type=int, default=200000)
    ap.add_argument("--reps", type=int, default=5)
    a = ap.parse_args()
    if not ctypes.windll.shell32.IsUserAnAdmin():
        sys.exit("needs an administrator prompt")
    exe = pmc_test.build()
    out = pmc_test.OUT / ("trace-" + time.strftime("%Y%m%d-%H%M%S"))
    out.mkdir(parents=True, exist_ok=True)
    etl, dumper = out / "diag.etl", out / "dumper.txt"
    subprocess.run([XPERF, "-stop"], capture_output=True)
    r = subprocess.run([XPERF, "-on", "PROC_THREAD+LOADER+CSWITCH", "-Pmc", "MACHINE_CLEARS.SMC", "CSWITCH", "strict", "-f", str(out / "kernel.etl")], capture_output=True, text=True)
    if r.returncode:
        sys.exit("xperf -on failed (register the source first: python validation/pmc_test.py --register-wpr):\n" + r.stdout + r.stderr)
    try:
        p = subprocess.run([str(exe), "--trace-markers", "--iters", str(a.iters), "--reps", str(a.reps)], capture_output=True, text=True)
    finally:
        subprocess.run([XPERF, "-d", str(etl)], capture_output=True)
    (out / "probe.txt").write_text(p.stdout + p.stderr, encoding="utf-8")
    subprocess.run([XPERF, "-i", str(etl), "-o", str(dumper), "-a", "dumper"], capture_output=True)
    m = re.search(r"thread id (\d+)", p.stdout)
    if not m:
        sys.exit("probe did not print its thread id:\n" + p.stdout + p.stderr)
    rows = pmc_events(dumper, int(m.group(1)))
    res, why = analyze(rows, len(CASES), a.reps)
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    print(p.stdout.split("trace-markers")[0].strip())
    if res is None:
        print("analysis failed:", why, "(%d counter events for the thread)" % len(rows))
        return 1
    summary = []
    for name, c in zip(CASES, res):
        med = statistics.median(c)
        print("%-48s %12.0f counted (median of %d) = %.4f per iteration   reps: %s" % (name, med, a.reps, med / a.iters, c))
        summary.append({"case": name, "count": med, "reps": c})
    (out / "result.json").write_text(json.dumps({"iters": a.iters, "cases": summary}, indent=1), encoding="utf-8")
    # the large trace files are not kept in the repository (.gitignore); the result and the probe output are
    for big in (etl, dumper, out / "kernel.etl"):
        try:
            big.unlink()
        except OSError:
            pass
    print("saved to", out)
    print("result: counts come from a kernel trace around each repetition; evidence about this machine only")
    return 0


if __name__ == "__main__":
    sys.exit(main())
