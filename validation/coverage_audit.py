"""Coverage audit for lean/PAPER_MAP.md (plan R14, D1).

  python validation/coverage_audit.py            check the table shape and write lean/CoverageRefs.lean
  python validation/coverage_audit.py --build    also compile CoverageRefs.lean (through build_modules.py) so that every named declaration exists

Checks: every row has an ID, a class (F, FC, FD, M, R, X, combinations allowed), no status `todo`; every F/FC/FD row names at least
one Lean declaration; every `open`/`partial` row is explained; every declaration named in the last column of an F/FC/FD row resolves
(`#check`); every P item of lean/errata/edits.json is mentioned in PAPER_MAP.md or a round note.
"""
import json, re, subprocess, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MAP = ROOT / "lean/PAPER_MAP.md"
OUT = ROOT / "lean/CoverageRefs.lean"
EDITS = ROOT / "lean/errata/edits.json"
CLASSES = {"F", "FC", "FD", "M", "R", "X"}


def rows():
    out = []
    for line in MAP.read_text(encoding="utf-8").splitlines():
        m = re.match(r"\|\s*(C\d+)\s*\|(.*)\|\s*$", line)
        if m:
            cells = [c.strip() for c in line.strip().split("|")[1:-1]]
            out.append(cells)
    return out


def decl_tokens(cell):
    toks = []
    for t in re.findall(r"`([^`]+)`", cell):
        t = t.strip()
        if "/" in t or t.endswith((".lean", ".json", ".md")) or " " in t or t.startswith("-") or not re.match(r"^[A-Za-z_][\w.']*$", t):
            continue
        toks.append(t)
    return toks


def main():
    bad = []
    rs = rows()
    ids = [r[0] for r in rs]
    if len(set(ids)) != len(ids):
        bad.append("duplicate claim IDs")
    names = []
    for r in rs:
        if len(r) < 7:
            bad.append(f"{r[0]}: expected 7 columns, got {len(r)}")
            continue
        cid, _loc, _claim, cls, _rnd, status, ev = r[:7]
        base = set(re.findall(r"\b(FC|FD|F|M|R|X)\b", cls))
        if not base:
            bad.append(f"{cid}: no class in '{cls}'")
        if status.lower().startswith("todo") or status == "":
            bad.append(f"{cid}: status '{status}'")
        toks = decl_tokens(ev)
        if base & {"F", "FC", "FD"} and not toks:
            bad.append(f"{cid}: class {cls} names no Lean declaration")
        if base & {"F", "FC", "FD"}:
            names += [(cid, t) for t in toks]
        if base == {"X"} and not ev:
            bad.append(f"{cid}: class X without a note")
        if (status.lower().startswith("open") or status.lower().startswith("partial")) and not ev:
            bad.append(f"{cid}: {status} without explanation")
    text = MAP.read_text(encoding="utf-8")
    for e in json.loads(EDITS.read_text(encoding="utf-8"))["edits"]:
        pid = e["id"].split(".")[0]
        if pid not in text and e["id"] not in text:
            bad.append(f"errata item {e['id']} is not mentioned in PAPER_MAP.md")
    srcs = (ROOT / "lean/SmcTamper.lean").read_text(encoding="utf-8").splitlines()
    mods = [l.split()[-1] for l in srcs if l.startswith("public import")]
    seen = []
    for cid, n in names:
        if n not in seen:
            seen.append(n)
    lines = ["module", ""] + ["import " + m for m in mods] + [""]
    lines += ["#check @%s" % (n if n.startswith("SmcTamper.") else "SmcTamper." + n) for n in seen]
    OUT.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"rows={len(rs)} declarations={len(seen)} problems={len(bad)}")
    for b in bad:
        print("  -", b)
    if "--build" in sys.argv:
        import os
        lean = Path(os.environ.get("ELAN_HOME", Path.home() / ".elan")) / "toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean.exe"
        env = dict(os.environ, LEAN_PATH=str(ROOT / "lean/.lake/proof-build/lib/lean"))
        r = subprocess.run([sys.executable, str(ROOT / "validation/limited_run.py"), "--cwd", str(ROOT / "lean"), "--timeout", "1500", "--",
                            str(lean), "CoverageRefs.lean"], cwd=ROOT, env=env)
        if r.returncode:
            bad.append("CoverageRefs.lean does not compile (a named declaration is missing)")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
