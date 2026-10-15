module
public import SmcTamper.Spec.Step

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

end SmcTamper
