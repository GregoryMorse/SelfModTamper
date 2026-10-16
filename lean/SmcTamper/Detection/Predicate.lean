module
public import SmcTamper.Spec.Detection

@[expose] public section

namespace SmcTamper

/-! ## C03 corrected, and P04: the predicate is not an "if and only if" -/

/-- **Completeness.**  An unmodified protected image, in its canonical state and measured within the threshold, is accepted. -/
theorem P_complete (u : CheckUnit) (m0 : Mem) (τ t : Nat) (ht : t ≤ τ) :
    u.P (u.value (u.reset m0)) τ (u.reset m0) t := ⟨rfl, ht⟩

/-- **Soundness for value-changing modifications.**  A memory whose run value differs from the expected one is rejected,
whatever the time. -/
theorem P_sound_value (u : CheckUnit) (expected : BitVec 64 × BitVec 8) (τ : Nat) (m : Mem) (t : Nat)
    (h : u.value m ≠ expected) : ¬ u.P expected τ m t := fun hp => h hp.1

/-- **Timing soundness.**  Any run that takes longer than `τ` (an emulator or a mediation slower than the threshold) is rejected,
whatever its value. -/
theorem P_sound_time (u : CheckUnit) (expected : BitVec 64 × BitVec 8) (τ : Nat) (m : Mem) (t : Nat)
    (h : τ < t) : ¬ u.P expected τ m t := fun hp => Nat.not_lt.mpr hp.2 h

/-- A memory with the first qword `0x8000000000000000` (even parity, negative: the kernel turns `ADC` into `CMP`), the second
qword either `0` or `0x8000000000000001`, all else `0`; the opcode byte at address `64` holds `ADC` (`0x13`). -/
def collMem (second : Nat) : Mem :=
  fun a => if a = 64 then 0x13 else if a = 7 then 0x80 else if a = 8 then (BitVec.ofNat 8 second) else if a = 15 then (BitVec.ofNat 8 (second / 2 ^ 56)) else 0

/-- The unit of the collision example: two qwords at address `0`, kernel opcode at address `64` (outside the region). -/
def collUnit : CheckUnit := ⟨64, 0, 16, 0x13⟩

/-- **P04.**  Two different images (they differ at addresses `8` and `15`) have the same run value, and both pass `P` with the
time equal: the predicate cannot be "true if and only if the code is unmodified". -/
theorem P_not_iff :
    collMem 0 ≠ collMem 0x8000000000000001 ∧
    collUnit.value (collMem 0) = collUnit.value (collMem 0x8000000000000001) := by
  refine ⟨fun h => ?_, ?_⟩
  · have := congrFun h 8
    simp [collMem] at this
  · decide +kernel

end SmcTamper
