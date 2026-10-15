module
public import SmcTamper.Spec.Bits

public section

namespace SmcTamper

/-- Table 2: the eight opcodes and their `Opcode[3:5]` fields. -/
theorem table2_fields :
    aluField 0x13 = 2 ∧ aluField 0x03 = 0 ∧ aluField 0x23 = 4 ∧ aluField 0x3B = 7 ∧
    aluField 0x0B = 1 ∧ aluField 0x1B = 3 ∧ aluField 0x2B = 5 ∧ aluField 0x33 = 6 := by
  decide

/-- The four opcodes the kernel cycles through are ADC, SBB, XOR, CMP. -/
theorem opcodeOf_values :
    opcodeOf 0 = 0x13 ∧ opcodeOf 1 = 0x1B ∧ opcodeOf 4 = 0x33 ∧ opcodeOf 5 = 0x3B := by decide

/-- The operation numbers that occur. -/
abbrev IsOp (op : Nat) : Prop := op = 0 ∨ op = 1 ∨ op = 4 ∨ op = 5

theorem opOf_opcodeOf (op : Nat) (h : IsOp op) : opOf (opcodeOf op) = op := by
  rcases h with rfl | rfl | rfl | rfl <;> decide

/-- `Opcode[3:5]` of the substituted opcode is `op ^^^ 2` (the base field 2 is ADC). -/
theorem aluField_opcodeOf (op : Nat) (h : IsOp op) : aluField (opcodeOf op) = op ^^^ 2 := by
  rcases h with rfl | rfl | rfl | rfl <;> decide

/-- The four opcodes (as a predicate on the byte). -/
abbrev IsKernelOpcode (b : BitVec 8) : Prop := b = 0x13 ∨ b = 0x1B ∨ b = 0x33 ∨ b = 0x3B

theorem isKernelOpcode_iff (b : BitVec 8) : IsKernelOpcode b ↔ ∃ op, IsOp op ∧ opcodeOf op = b := by
  constructor
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, by simp [IsOp], by decide⟩
    · exact ⟨1, by simp [IsOp], by decide⟩
    · exact ⟨4, by simp [IsOp], by decide⟩
    · exact ⟨5, by simp [IsOp], by decide⟩
  · rintro ⟨op, h, rfl⟩
    rcases h with rfl | rfl | rfl | rfl <;> decide

/-- The toggle is always in `{0,1,4,5}`, so the op number stays closed under XOR (the `default: res = 0` of
Fig. 3 is unreachable). -/
theorem toggle_isOp (res : BitVec 64) : IsOp (toggle res) := by
  unfold toggle; unfold IsOp
  cases pf res <;> cases sf res <;> decide

theorem isOp_xor_toggle (op : Nat) (h : IsOp op) (res : BitVec 64) : IsOp (op ^^^ toggle res) := by
  have := toggle_isOp res
  unfold IsOp at *
  rcases h with rfl | rfl | rfl | rfl <;> rcases this with h | h | h | h <;> rw [h] <;> decide

/-- Toggling the opcode byte by `toggle res <<< 3` is the same as xoring the op number by `toggle res`. -/
theorem opcodeOf_xor_toggle (op : Nat) (h : IsOp op) (res : BitVec 64) :
    opcodeOf (op ^^^ toggle res) = opcodeOf op ^^^ (BitVec.ofNat 8 (toggle res) <<< 3) := by
  have := toggle_isOp res
  unfold IsOp at *
  rcases h with rfl | rfl | rfl | rfl <;> rcases this with h | h | h | h <;> rw [h] <;> decide

/-- The kernel's XOR mask touches bits 3 and 5 only: it is one of `0, 8, 32, 40`. -/
theorem toggle_shift_mask (res : BitVec 64) :
    BitVec.ofNat 8 (toggle res) <<< 3 = 0 ∨ BitVec.ofNat 8 (toggle res) <<< 3 = 8 ∨
    BitVec.ofNat 8 (toggle res) <<< 3 = 32 ∨ BitVec.ofNat 8 (toggle res) <<< 3 = 40 := by
  have := toggle_isOp res
  unfold IsOp at this
  rcases this with h | h | h | h <;> rw [h] <;> decide

/-- The four opcodes are closed under XOR with the mask. -/
theorem kernelOpcode_xor_closed (b : BitVec 8) (h : IsKernelOpcode b) (res : BitVec 64) :
    IsKernelOpcode (b ^^^ (BitVec.ofNat 8 (toggle res) <<< 3)) := by
  rcases (isKernelOpcode_iff b).1 h with ⟨op, hop, rfl⟩
  rw [← opcodeOf_xor_toggle op hop res]
  exact (isKernelOpcode_iff _).2 ⟨_, isOp_xor_toggle op hop res, rfl⟩

end SmcTamper
