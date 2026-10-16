"""Read validation/.build/native/TP.obj (ml64 output of SelfModTamper/TP.asm): the .text bytes and the offsets of the
public symbols TPComp and TPCompLoop (COFF symbol table). Writes validation/layout/tp_x64.json.
Evidence, not proof: these are the bytes MASM emitted."""
import json, struct
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
obj = (ROOT / "validation/.build/native/TP.obj").read_bytes()
nsec = struct.unpack_from("<H", obj, 2)[0]
symptr, nsym = struct.unpack_from("<II", obj, 8)
opt = struct.unpack_from("<H", obj, 16)[0]
text = None
for i in range(nsec):
    o = 20 + opt + 40 * i
    name = obj[o:o + 8].rstrip(b"\0")
    size, ptr = struct.unpack_from("<II", obj, o + 16)
    if name.startswith(b".text"):
        nrel, = struct.unpack_from("<H", obj, o + 32); rptr, = struct.unpack_from("<I", obj, o + 24)
        text = (i + 1, bytearray(obj[ptr:ptr + size]), rptr, nrel)
assert text, "no .text"
strtab = symptr + 18 * nsym
syms = {}
byidx = {}
i = 0
while i < nsym:
    o = symptr + 18 * i
    nm = obj[o:o + 8]
    if nm[:4] == b"\0\0\0\0":
        off = struct.unpack_from("<I", nm, 4)[0]
        e = obj.index(b"\0", strtab + off)
        name = obj[strtab + off:e].decode()
    else:
        name = nm.rstrip(b"\0").decode()
    value, sec, typ, cls, aux = struct.unpack_from("<IhHBB", obj, o + 8)
    byidx[i] = value if sec == text[0] else None
    if sec == text[0]:
        syms[name] = value
    i += 1 + aux
# Resolve the REL32 relocations (the labels are in the same section; MASM leaves the addend in the field).
unresolved = 0
for r in range(text[3]):
    va, si, ty = struct.unpack_from("<IIH", obj, text[2] + 10 * r)
    S = byidx.get(si)
    if S is None or not (4 <= ty <= 9):
        unresolved += 1; continue
    A = struct.unpack_from("<i", text[1], va)[0]
    val = (A + S - (va + 4 + (ty - 4))) & 0xFFFFFFFF
    struct.pack_into("<I", text[1], va, val)
print("relocations", text[3], "unresolved", unresolved, "text", len(text[1]))
a, b = syms["TPComp"], syms["TPCompLoop"]
out = {"source": "ml64 /c /Sa TP.asm (validation/native_harness.py), REL32 relocations resolved by extract_tp.py", "text_size": len(text[1]),
       "symbols": {k: v for k, v in syms.items() if k in ("TPComp", "TPCompLoop")},
       "relocations": text[3], "unresolved": unresolved, "tpcomp": list(text[1][a:b]), "tpcomploop": list(text[1][b:])}
(ROOT / "validation/layout/tp_x64.json").write_text(json.dumps(out) + "\n")
dyn = json.loads((ROOT / "validation/layout/dyn_x64.json").read_text())["bytes"]
stat = out["tpcomploop"]
print("static loop bytes", len(stat), "dyn bytes", len(dyn))
n = min(len(stat), len(dyn))
diff = [i for i in range(n) if stat[i] != dyn[i]]
print("diffs", len(diff), diff[:40])
print("static tail", stat[-40:], "dyn tail", dyn[-40:])
