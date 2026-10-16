module
public import SmcTamper.Spec.Kernel

@[expose] public section

namespace SmcTamper

/-! ## Detection: checksum units, the predicate `P`, the alarm policy, reset

A *checksum unit* protects the region `[start, start + size)` with the static SMC kernel (Level 1) whose own opcode byte is at
`opAddr`; `canon` is the opcode byte of the canonical state.  A run starts with the sum `0` and the data pointer at `start`.
Its *value* is the final sum together with the final opcode byte (the unit's SMC state).  The predicate `P` accepts a run when
the value equals the expected value and the measured time is at most `τ`.  Which adversary and which assumptions make `P`
meaningful is the threat model (R11b), not here. -/

structure CheckUnit where
  opAddr : Nat
  start : Nat
  size : Nat
  canon : BitVec 8

/-- The final machine state of one run on the memory `m`. -/
def CheckUnit.run (u : CheckUnit) (m : Mem) : KState := staticRun u.opAddr (u.size / 8) ⟨m, u.start, 0⟩

/-- The value of a run: final sum and final opcode byte. -/
def CheckUnit.value (u : CheckUnit) (m : Mem) : BitVec 64 × BitVec 8 :=
  ((u.run m).sum, (u.run m).mem u.opAddr)

/-- The canonical memory of a unit: the protected image `m` with the opcode byte in its canonical state. -/
def CheckUnit.reset (u : CheckUnit) (m : Mem) : Mem := wr8 m u.opAddr u.canon

/-- The tamper-proofing predicate on one run: the value matches the expected one and the measured time is within `τ`. -/
def CheckUnit.P (u : CheckUnit) (expected : BitVec 64 × BitVec 8) (τ : Nat) (m : Mem) (t : Nat) : Prop :=
  u.value m = expected ∧ t ≤ τ

/-- `k` consecutive failures ending at run `t`: the alarm of the policy. -/
def alarm (k : Nat) (ok : Nat → Bool) (t : Nat) : Prop := k ≤ t + 1 ∧ ∀ i, i < k → ok (t - i) = false

end SmcTamper
