#!/usr/bin/env python3
"""Translate SelfModTamper/TP.asm (MASM, x64) into GNU as, Intel syntax.

Only the MASM subset used by TP.asm is handled: `PROC USES`, `ENDP`, `ret`, `END`, `.code`, `option`, `$`-relative and
label-relative memory operands (MASM encodes them RIP-relative in 64-bit mode, so they become `[rip + ...]`).
The result is checked byte-for-byte against the MASM build by `--dump-kernels` (see validation/pmc/README.md).

    python3 scripts/masm2gas.py SelfModTamper/TP.asm build/TP.gas.S
"""
import re
import sys


def main(src, dst):
    out = [".intel_syntax noprefix", ".text"]
    uses = []
    selfn = 0
    for raw in open(src, encoding="utf-8", errors="replace").read().splitlines():
        line = raw.split(";", 1)[0].rstrip()
        s = line.strip()
        if not s:
            continue
        low = s.lower()
        if low.startswith("option ") or low == ".code" or low == "end":
            continue
        m = re.match(r"(\w+)\s+proc\s+uses\s+(.+)$", s, re.I)
        if m:
            name = m.group(1)
            uses = m.group(2).replace(",", " ").split()
            out += [".globl " + name, ".type " + name + ", @function", name + ":"] + ["push " + r for r in uses]
            continue
        if re.match(r"\w+\s+endp$", s, re.I):
            continue
        if low == "ret":
            out += ["pop " + r for r in reversed(uses)] + ["ret"]
            continue
        # `$-a-b-c` : address of the start of the current instruction minus the sum
        m = re.search(r"\[\$((?:-\d+)+)\]", s)
        if m:
            selfn += 1
            total = sum(int(x) for x in re.findall(r"-\d+", m.group(1)))
            tag = ".Lself%d" % selfn
            out.append(tag + ":")
            s = s.replace(m.group(0), "[rip + %s%d]" % (tag, total))
        else:
            s = re.sub(r"\[(\w+)([+-]\d+)?\]", lambda mm: "[rip + %s%s]" % (mm.group(1), mm.group(2) or "") if re.match(r"[A-Za-z_]\w*$", mm.group(1)) and mm.group(1).lower() not in REGS else mm.group(0), s)
        out.append(s)
    out.append(".size TPCompLoop, .-TPCompLoop")
    open(dst, "w", encoding="utf-8", newline="\n").write("\n".join(out) + "\n")


REGS = set("rax rbx rcx rdx rsi rdi rbp rsp r8 r9 r10 r11 r12 r13 r14 r15 eax ebx ecx edx esi edi ebp esp".split())

if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
