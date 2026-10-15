module
public import SmcTamper.Spec.Bits

@[expose] public section

namespace SmcTamper

/-! ## The C++ emulation of Fig. 3, transcribed

`op` is the C variable (the persistent opcode state); `p` is the address held by `pData` (advanced by 8 per
iteration, `PULONG64`). `opAddr` is `pTPCompOffset + 0xF`: `pModOffset = opAddr & ~7`,
`pModByteOffset = (opAddr & 7) * 8 + 3`. -/

structure CState where
  p : Nat
  sum : BitVec 64
  op : Nat

/-- The `switch (op)`: `(res, new sum)`; `default: res = 0` leaves the sum unchanged. -/
def cSwitch (op : Nat) (sum v : BitVec 64) : BitVec 64 × BitVec 64 :=
  match op with
  | 0 => (sum + v, sum + v)
  | 1 => (sum - v, sum - v)
  | 4 => (sum ^^^ v, sum ^^^ v)
  | 5 => (sum - v, sum)
  | _ => (0, sum)

/-- `op ^= (!paritybyte((unsigned char)res) << 2) | ((res & 0x8000000000000000ULL) != 0)`. -/
def cOpNext (op : Nat) (res : BitVec 64) : Nat :=
  op ^^^ (((if paritybyteC (res.setWidth 8) then 0 else 1) <<< 2) |||
    (if res &&& 0x8000000000000000#64 != 0 then 1 else 0))

/-- One iteration of the C loop body against the (unmodified) memory image `m`. -/
def tpCompCStep (m : Mem) (opAddr : Nat) (c : CState) : CState :=
  let raw := rd64 m c.p
  let v := if c.p = opAddr / 8 * 8 then cSubst raw (opAddr % 8) c.op else raw
  let r := cSwitch c.op c.sum v
  { p := c.p + 8, sum := r.2, op := cOpNext c.op r.1 }

def tpCompCIter (m : Mem) (opAddr : Nat) : Nat → CState → CState
  | 0, c => c
  | n + 1, c => tpCompCIter m opAddr n (tpCompCStep m opAddr c)

/-- `TPCompC(pData = p0, ulSize = size, pResult)` with persistent `op = op0`: returns `(*pResult, final op)`.
The loop runs `⌈size / 8⌉` times. -/
def tpCompC (m : Mem) (opAddr p0 size op0 : Nat) : BitVec 64 × Nat :=
  let c := tpCompCIter m opAddr ((size + 7) / 8) ⟨p0, 0, op0⟩
  (c.sum, c.op)

end SmcTamper
