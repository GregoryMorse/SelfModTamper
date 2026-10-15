module
public import SmcTamper.Spec.Bits
public import SmcTamper.Bits.Opcode

public section


namespace SmcTamper

/-- Byte `j` (little-endian) of a 64-bit word. -/
def byteAt (x : BitVec 64) (j : Nat) : BitVec 8 := (x >>> (8 * j)).setWidth 8

theorem getLsbD_byteAt (x : BitVec 64) (j k : Nat) (hk : k < 8) :
    (byteAt x j).getLsbD k = x.getLsbD (8 * j + k) := by
  simp [byteAt, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hk, Nat.add_comm]

/-- Bit-level form of "byte `j` is one of ADC, SBB, XOR, CMP": bits 0, 1 and 4 set, bits 2, 6 and 7 clear. -/
theorem kernelOpcode_bits (b : BitVec 8) (h : IsKernelOpcode b) :
    b.getLsbD 0 = true ∧ b.getLsbD 1 = true ∧ b.getLsbD 4 = true ∧
    b.getLsbD 2 = false ∧ b.getLsbD 6 = false ∧ b.getLsbD 7 = false := by
  rcases h with rfl | rfl | rfl | rfl <;> decide

theorem const_bit_false (c : Nat) (n k : Nat) (hc : c < 2 ^ n) (hk : n ≤ k) : (BitVec.ofNat 64 c).getLsbD k = false := by
  rw [BitVec.getLsbD_ofNat]
  by_cases h : k < 64
  · simp only [h, decide_true, Bool.true_and]
    apply Nat.testBit_lt_two_pow
    exact Nat.lt_of_lt_of_le hc (Nat.pow_le_pow_right (by omega) hk)
  · simp [h]

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The key lemma for Fig. 3: for a word whose byte `j < 8` is one of the four kernel opcodes, the C substitution
`(x & ~(5 << (8j+3))) | (op << (8j+3))` replaces that byte by `opcodeOf op` and changes nothing else. -/
theorem cSubst_eq_setByte (x : BitVec 64) (j : Nat) (hj : j < 8) (op : Nat) (hop : IsOp op)
    (hx : IsKernelOpcode (byteAt x j)) : cSubst x j op = setByte x j (opcodeOf op) := by
  obtain ⟨b0, b1, b4, b2, b6, b7⟩ := kernelOpcode_bits _ hx
  rw [getLsbD_byteAt x j _ (by omega)] at b0 b1 b4 b2 b6 b7
  have hlt : ∀ k, ¬ (8 * j + k < 8 * j) := by omega
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  unfold cSubst setByte opcodeOf
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_xor, BitVec.getLsbD_setWidth, hi]
  by_cases h1 : i < 8 * j
  · have h3 : i < 8 * j + 3 := by omega
    simp [h1, h3]
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (Nat.not_lt.1 h1)
    by_cases hd : d < 8
    · rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hop with rfl | rfl | rfl | rfl <;>
      · simp [Nat.add_sub_cancel_left, Nat.add_sub_add_left, hlt] at *
        try simp_all
    · have e1 : 8 * j + d - 8 * j = d := by omega
      have e2 : 8 * j + d - (8 * j + 3) = d - 3 := by omega
      have c5 := const_bit_false 5 3 (d - 3) (by decide) (by omega)
      have c255 := const_bit_false 255 8 d (by decide) (by omega)
      have cop : (BitVec.ofNat 64 op).getLsbD (d - 3) = false :=
        const_bit_false op 3 (d - 3) (by rcases hop with rfl | rfl | rfl | rfl <;> decide) (by omega)
      rw [e1, e2]
      have hd3 : ¬ d < 3 := by omega
      have c19' : (19#8).getLsbD d = false := BitVec.getLsbD_of_ge _ _ (by omega)
      simp [c5, c255, cop, hd, hd3, hlt, c19']

end SmcTamper
