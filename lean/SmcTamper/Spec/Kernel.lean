module
public import SmcTamper.Spec.Step
public import SmcTamper.Spec.Layout

@[expose] public section

namespace SmcTamper

/-! ## Level 1: the abstract SMC checksum machine (static kernel)

State: the byte memory (which also holds the kernel's own opcode byte), the data pointer and the running sum.
One step reads the opcode byte at `opAddr` from the *current* memory, combines the next data qword with the sum
using the ALU function that opcode selects (ADC and SBB with carry clear, XOR, or CMP, which leaves the sum
unchanged), and XORs the opcode byte with the toggle `(PF << 2 | SF) << 3` of the result. -/

structure KState where
  mem : Mem
  ptr : Nat
  sum : BitVec 64

/-- Result and new sum of the ALU function selected by an opcode byte (`aluField`), with carry clear. -/
def kAlu (opb : BitVec 8) (sum d : BitVec 64) : BitVec 64 × BitVec 64 :=
  let p := aluW (Fin.ofNat 8 (aluField opb)) sum d false
  (p.1, if aluField opb = 7 then sum else p.1)

/-- One iteration of the static kernel (Fig. 2) with the opcode byte at address `opAddr`. -/
def staticStep (opAddr : Nat) (k : KState) : KState :=
  let opb := k.mem opAddr
  let r := kAlu opb k.sum (rd64 k.mem k.ptr)
  { mem := wr8 k.mem opAddr (opb ^^^ (BitVec.ofNat 8 (toggle r.1) <<< 3)), ptr := k.ptr + 8, sum := r.2 }

/-- `n` iterations. -/
def staticRun (opAddr : Nat) : Nat → KState → KState
  | 0, k => k
  | n + 1, k => staticRun opAddr n (staticStep opAddr k)

/-! ## Level 1: the unrolled kernel (`TPCompLoop`, Fig. 4)

`base` is the address of the first byte of the function. Unit `u` (`u < 296`) reads its own opcode byte at
`base + opOff u` and XORs the toggle into the opcode byte of unit `(u + 148) mod 296` (the same position in the other page). -/

/-- One unrolled unit. -/
def unitStep (base u : Nat) (k : KState) : KState :=
  let r := kAlu (k.mem (base + opOff u)) k.sum (rd64 k.mem k.ptr)
  let tgt := base + opOff ((u + perPage) % numUnits)
  { mem := wr8 k.mem tgt (k.mem tgt ^^^ (BitVec.ofNat 8 (toggle r.1) <<< 3)), ptr := k.ptr + 8, sum := r.2 }

/-- `n` consecutive units starting at unit `u` (wrapping from 295 to 0, as the code does by jumping back to `L0`). -/
def unitsFrom (base : Nat) : Nat → Nat → KState → KState
  | _, 0, k => k
  | u, n + 1, k => unitsFrom base ((u + 1) % numUnits) n (unitStep base u k)

/-- `q` full passes over all 296 units. -/
def fullPasses (base : Nat) : Nat → KState → KState
  | 0, k => k
  | q + 1, k => fullPasses base q (unitsFrom base 0 numUnits k)

/-- The 64-bit `XOR QWORD PTR [a], RDI`: XOR byte `x - a` of `v` into each of the eight bytes from `a`. -/
def xorQword (m : Mem) (a : Nat) (v : BitVec 64) : Mem :=
  fun x => if a ≤ x ∧ x < a + 8 then m x ^^^ (v >>> (8 * (x - a))).setWidth 8 else m x

/-- The full pass count for `size` bytes: the intro subtracts 2368 while the remainder stays positive. -/
def passCount (size : Nat) : Nat := (size - 1) / 2368

/-- Bytes left for the final pass, and its number of units (`shr rdi, 3`). -/
def finalBytes (size : Nat) : Nat := size - 2368 * passCount size
def finalUnits (size : Nat) : Nat := finalBytes size / 8

/-- The termination patch (address and mask) for a final pass of `n ≥ 1` units: unit `n - 1`'s `LEA` and the next byte. -/
def patchAddr (base n : Nat) : Nat := base + leaOff (n - 1)
def patchVal (n : Nat) : BitVec 64 := patchMask (BitVec.ofNat 32 (patchImm - rsiOf (n - 1)))

/-- One call of the unrolled kernel on a state whose pointer is the start of the data: `passCount` full passes, then
the intro applies the termination patch for the final `n` units, the units run, and the epilogue applies the same XOR
again. (The patched unit's `LEA`, which the jump replaces, only advances the pointer, which is dead afterwards.) -/
def callUnrolled (base size : Nat) (k : KState) : KState :=
  let n := finalUnits size
  let k1 := fullPasses base (passCount size) k
  let k2 := unitsFrom base 0 n { k1 with mem := xorQword k1.mem (patchAddr base n) (patchVal n) }
  { k2 with mem := xorQword k2.mem (patchAddr base n) (patchVal n) }

end SmcTamper
