module

@[expose] public section

namespace SmcTamper

/-! ## Layout of the unrolled loop (`TPCompLoop`, `gen_asm`)

Offsets are relative to the first byte of the function (the `PUSH RBX`). The intro is `introLen` bytes, a page is
`pageSize` bytes, one unrolled unit is `unitLen` bytes; `perPage = ⌊(pageSize − introLen) / unitLen⌋` units fit in the
first page, the rest of it is padded with NOPs, the second page holds `perPage` more units. -/

def pageSize : Nat := 4096
def introLen : Nat := 95
def unitLen : Nat := 27
def perPage : Nat := (pageSize - introLen) / unitLen
def numUnits : Nat := 2 * perPage
def nopPad : Nat := pageSize - (introLen + perPage * unitLen)

/-- The intro's `ESI` value for unit `k` (`IMUL RSI,RDI,27`, plus the `ADD ESI,5` once past the first page). -/
def rsiOf (k : Nat) : Nat := unitLen * k + (if perPage ≤ k then nopPad else 0)

/-- Offset of the first byte of unit `k`. -/
def unitStart (k : Nat) : Nat := introLen + rsiOf k

/-- Offset of the opcode byte of unit `k`'s `ADC` (one past its REX prefix). -/
def opOff (k : Nat) : Nat := unitStart k + 1

/-- Offset of the `LEA RCX,[RCX+8]` of unit `k` that the termination patch overwrites. -/
def leaOff (k : Nat) : Nat := unitStart k + 23

/-- The constant of the termination patch (`mov rax, imm`): `disp = patchImm − rsi`. -/
def patchImm : Nat := 7974

/-- The mask XORed into the five bytes `48 8D 49 08 48`: `(0xE9 ^ 0x4808498D48) ^ (disp << 8)`. -/
def patchMask (disp : BitVec 32) : BitVec 64 :=
  (0xE9#64 ^^^ 0x4808498D48#64) ^^^ (disp.setWidth 64 <<< 8)

/-- Offset (from the function start) of the byte after the `JMP L0` at the end of page 2. -/
def jmpEnd : Nat := 8097

end SmcTamper
