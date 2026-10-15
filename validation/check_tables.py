"""Re-read Tables 4-6 and the Fig. 5 listing from the arXiv v1 TeX and compare with
validation/data/paper_tables.json (guards against transcription errors).  Usage: python validation/check_tables.py"""
import json, re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TEX = ROOT / "paper/arxiv-v1/SelfModifyingCodeTamperProofingManuscriptUpdated.tex"


def row_cells(line: str) -> list[str]:
    return [c.strip() for c in re.sub(r"\\\\|\\hline", "", line).split("&")]


def main() -> int:
    lines = TEX.read_text(encoding="utf-8").splitlines()
    data = json.loads((ROOT / "validation/data/paper_tables.json").read_text(encoding="utf-8"))
    bad = []
    for key in ("table4_static", "table5_dynamic"):
        for r in data[key]["rows"]:
            cells = row_cells(lines[r["tex_line"] - 1])
            want = [r["timer"]] + [str(r[g][k]) for g in ("smc", "non_smc") for k in ("avg", "min", "max")]
            if cells != want:
                bad.append((key, r["timer"], cells, want))
    for r in data["table6_clears"]["rows"]:
        if row_cells(lines[r["tex_line"] - 1]) != [r["variant"], str(r["count"])]:
            bad.append(("table6", r["variant"]))
    f = data["fig5"]
    block = "\n".join(lines[f["tex_lines"][0] - 1:f["tex_lines"][1]])
    for pat in (f["code_segment_base"], f["size"], f["end"], f["intro_bytes"], f["code_size"],
                f"Number of pages: {f['pages']}", f"Unrolled loop size per page: {f['unrolled_loop_size_per_page']}",
                f"page size for this system is {f['page_size']} bytes"):
        if pat not in block:
            bad.append(("fig5", pat))
    claims = data["text_claims"]
    for k in ("static_vs_basic_c", "dynamic_vs_nonsmc", "dynamic_vs_static"):
        c = claims[k]
        if not re.search(re.escape(c["printed"]) + r"\\times", lines[c["tex_line"] - 1]):
            bad.append(("claim", k))
    e = claims["estimator"]
    txt = lines[e["tex_line"] - 1]
    for n in (e["numerator"][0], e["numerator"][1]):
        if f"{n:,}".replace(",", "{,}") not in txt:
            bad.append(("estimator", n))
    print("tables check:", "OK" if not bad else bad)
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
