"""Assemble writeexc.asm (x86, x64) with listings; stream-parse label offsets from the listing symbol
table and read .text bytes from the COFF object. Emits validation/layout/{x86,x64}.json.
Listings (~170 MB) stay in validation/.build and are never committed."""
import json, re, struct, subprocess, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
NAME = sys.argv[1] if len(sys.argv) > 1 else "lst"   # lst = published source, lstc = corrected source
B = ROOT / "validation/.build" / NAME
SUF = "c" if NAME == "lstc" else ""
SYM = re.compile(r"^\s*([A-Za-z_@$?][\w@$?]*) [ .]*\s*L\s+(?:Near)?\s*([0-9A-F]{8}) _TEXT")
FAMILIES = ["notres", "nzres", "shlres", "shlres4", "shlres5", "shlres6", "shlres7", "xorarg1", "orarg1", "andarg1"]
SINGLES = ["notarg", "notargshl", "notres", "notret", "nzarg", "nzargshl", "nzres", "nzret", "shlarg", "shlres", "shlret",
           "shlarg4", "shlres4", "shlret4", "shlarg5", "shlres5", "shlret5", "xorarg1", "xorarg2", "xorargshl1", "xorargshl2",
           "xorargshl2jmp", "xorhead", "xorloop", "xorj", "xorres", "xorret", "carry1", "carry1retval", "nocry1", "hascarry1",
           "carry2", "carry2retval", "nocry2", "hascarry2"]
def text_bytes(obj):
    d = Path(obj).read_bytes(); n = struct.unpack_from("<H", d, 2)[0]; opt = struct.unpack_from("<H", d, 16)[0]
    for i in range(n):
        o = 20 + opt + 40 * i; name = d[o:o+8].rstrip(b"\0")
        size, ptr = struct.unpack_from("<II", d, o + 16)
        if name == b".text" or name.startswith(b".text"): return d[ptr:ptr+size]
    raise SystemExit("no .text")
def labels(lst):
    out = {}
    with open(lst, encoding="latin-1") as f:
        for line in f:
            m = SYM.match(line)
            if m: out[m.group(1)] = int(m.group(2), 16)
    return out
def main():
    ROOT.joinpath("validation/layout").mkdir(exist_ok=True)
    for arch in ("x86", "x64"):
        lab = labels(B / f"{arch}.lst"); text = text_bytes(B / f"{arch}.obj")
        res = {"arch": arch, "text_size": len(text), "labels": {k: lab[k] for k in SINGLES if k in lab}, "tables": {}}
        for fam in FAMILIES:
            pat = re.compile(re.escape(fam) + r"_(\d+)$")
            ent = sorted((int(m.group(1)), o) for k, o in lab.items() if (m := pat.match(k)))
            if len(ent) < 2: continue
            res["tables"][fam] = {"offsets": [o for _, o in ent], "indices": [i for i, _ in ent]}
        (ROOT / f"validation/layout/{arch}{SUF}.json").write_text(json.dumps(res, indent=0) + "\n")
        # report stride anomalies
        print(arch, "text", len(text), "labels", len(lab))
        for fam, t in res["tables"].items():
            ds = [b - a for a, b in zip(t["offsets"], t["offsets"][1:])]
            print(" ", fam, "n=%d" % len(ds + [0]), "strides", {d: ds.count(d) for d in sorted(set(ds))},
                  "anomalies at", [t["indices"][i] for i, d in enumerate(ds) if d != max(set(ds), key=ds.count)][:12])
if __name__ == "__main__": main()
