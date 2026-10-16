"""Pattern comparison of this machine's product runs with the paper's Tables 4-5 (evidence only, not proof; no results are regenerated).
Input: validation/native/runs/{pre_release,pre_debug,post_release,post_debug}.txt (stdout of SelfModTamper.exe, unelevated, driver absent).
Output: validation/data/native_runs.json. Usage: python validation/native_consistency.py"""
import json, re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
RUNS = ROOT / "validation/native/runs"
# Paper (arXiv v1), RDTSC average column: Table 4 (static, 220 KB segment) and Table 5 (dynamic), SMC vs non-SMC.
PAPER = {"T4_smc": 8305286, "T4_nonsmc": 1052981, "T5_smc": 467241, "T5_nonsmc": 42300670, "segment_kb": 220}


def parse(path: Path) -> dict:
    text = path.read_text(errors="replace")
    seg = re.search(r"Code segment base: 0x[0-9A-F]+ size: 0x([0-9A-F]+)", text)
    out = {"segment_bytes": int(seg.group(1), 16) if seg else None, "rows": {}}
    for block in text.split("\n\n"):
        lines = [l for l in block.strip().splitlines() if not l.startswith("MACHINE_CLEARS")]
        if len(lines) >= 2 and re.fullmatch(r"[A-Za-z ]+", lines[0]) and re.match(r"\d+ \d+ \d+", lines[1]):
            avg, mn, mx = (int(x) for x in lines[1].split())
            out["rows"][lines[0]] = {"rdtsc_avg": avg, "min": mn, "max": mx}
    return out


def main() -> None:
    res = {"paper": PAPER, "runs": {}}
    for name in ("pre_release", "pre_debug", "post_release", "post_debug"):
        f = RUNS / f"{name}.txt"
        if not f.exists():
            continue
        r = parse(f)
        rows = r["rows"]
        if name.startswith("pre_"):  # L01: before the fix the last two printed labels were swapped; relabel to the measured kernels
            rows["Dyn SMC Loop"], rows["SMC Loop"] = rows["SMC Loop"], rows["Dyn SMC Loop"]
            r["relabelled_L01"] = True
        r["scaled_to_220KB"] = {k: round(v["rdtsc_avg"] * PAPER["segment_kb"] * 1024 / r["segment_bytes"]) for k, v in rows.items()}
        if {"C Loop", "SMC", "Dyn SMC Loop", "SMC Loop"} <= rows.keys():
            d = rows["Dyn SMC Loop"]["rdtsc_avg"]
            r["ratios"] = {"CLoop_over_dynamic": round(rows["C Loop"]["rdtsc_avg"] / d, 1),
                           "SMCsingle_over_dynamic": round(rows["SMC"]["rdtsc_avg"] / d, 1),
                           "dynamic_over_static": round(d / rows["SMC Loop"]["rdtsc_avg"], 3)}
        res["runs"][name] = r
    res["paper_ratios"] = {"T5_nonsmc_over_smc": round(PAPER["T5_nonsmc"] / PAPER["T5_smc"], 1),
                           "T4_smc_over_T5_smc": round(PAPER["T4_smc"] / PAPER["T5_smc"], 1)}
    (ROOT / "validation/data/native_runs.json").write_text(json.dumps(res, indent=1) + "\n")
    print(json.dumps({k: v.get("ratios") for k, v in res["runs"].items()} | {"paper": res["paper_ratios"]}, indent=1))


main()
