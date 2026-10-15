module

public section

namespace SmcTamper

/-- Byte-addressed memory: the content at each natural-number address. -/
abbrev Mem := Nat → BitVec 8

/-- Little-endian 64-bit read: the byte at `a` is the least significant. -/
@[expose] def rd64 (m : Mem) (a : Nat) : BitVec 64 :=
  (m a).setWidth 64 ||| ((m (a + 1)).setWidth 64 <<< 8) ||| ((m (a + 2)).setWidth 64 <<< 16) |||
  ((m (a + 3)).setWidth 64 <<< 24) ||| ((m (a + 4)).setWidth 64 <<< 32) |||
  ((m (a + 5)).setWidth 64 <<< 40) ||| ((m (a + 6)).setWidth 64 <<< 48) |||
  ((m (a + 7)).setWidth 64 <<< 56)

/-- Write one byte. -/
@[expose] def wr8 (m : Mem) (a : Nat) (b : BitVec 8) : Mem := fun x => if x = a then b else m x

/-- The number of one bits in the byte is even (the x86 parity-flag convention; PF looks at the low byte only). -/
@[expose] def evenParity8 (b : BitVec 8) : Bool :=
  !(b.getLsbD 0 ^^ b.getLsbD 1 ^^ b.getLsbD 2 ^^ b.getLsbD 3 ^^ b.getLsbD 4 ^^ b.getLsbD 5 ^^ b.getLsbD 6 ^^
    b.getLsbD 7)

/-- Parity flag of a result: even parity of its low byte. -/
@[expose] def pf {w : Nat} (x : BitVec w) : Bool := evenParity8 (x.setWidth 8)

/-- Sign flag of a result: its most significant bit. -/
@[expose] def sf {w : Nat} (x : BitVec w) : Bool := x.msb

/-- The two-bit operation number held in bits 3 (weight 1) and 5 (weight 4) of an ALU opcode byte. -/
@[expose] def opOf (b : BitVec 8) : Nat :=
  (if b.getLsbD 3 then 1 else 0) ||| (if b.getLsbD 5 then 4 else 0)

/-- The opcode byte for operation number `op`: `ADC = 0x13` with bits 3 and 5 toggled by `op`
(0 = ADC `13`, 1 = SBB `1B`, 4 = XOR `33`, 5 = CMP `3B`). -/
@[expose] def opcodeOf (op : Nat) : BitVec 8 := 0x13 ^^^ (BitVec.ofNat 8 op <<< 3)

/-- The next toggle of the operation number: parity (weight 4) and sign (weight 1) of the result. -/
@[expose] def toggle (res : BitVec 64) : Nat := (if pf res then 4 else 0) ||| (if sf res then 1 else 0)

/-- Bits 3 to 5 of a byte: the `reg` field of the ALU opcode (Table 2, column Opcode[3:5]). -/
@[expose] def aluField (b : BitVec 8) : Nat := (b.toNat >>> 3) % 8

/-- The C helper `paritybyte` of the paper's code (nibble-fold and the table constant `0x6996`):
it returns the odd-parity bit of the byte. -/
@[expose] def paritybyteC (v : BitVec 8) : Bool :=
  let w := (v ^^^ (v >>> 4)) &&& 0xf
  ((0x6996 : Nat) >>> w.toNat) % 2 == 1

/-- Replace byte `j` (little-endian, `j < 8`) of a 64-bit word. -/
@[expose] def setByte (x : BitVec 64) (j : Nat) (b : BitVec 8) : BitVec 64 :=
  (x &&& ~~~(0xFF#64 <<< (8 * j))) ||| (b.setWidth 64 <<< (8 * j))

/-- The C substitution of Fig. 3: keep `x`, clear bits `8j+3` and `8j+5`, and OR in `op` shifted to bit `8j+3`
(`pDataVal = (*pData & preserve) | (op << pModByteOffset)` with `pModByteOffset = 8 j + 3`). -/
@[expose] def cSubst (x : BitVec 64) (j : Nat) (op : Nat) : BitVec 64 :=
  (x &&& ~~~(5#64 <<< (8 * j + 3))) ||| (BitVec.ofNat 64 op <<< (8 * j + 3))

end SmcTamper
