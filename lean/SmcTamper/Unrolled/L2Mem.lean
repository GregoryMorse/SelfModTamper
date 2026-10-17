module
public import SmcTamper.Unrolled.L2Unit

@[expose] public section

namespace SmcTamper

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Level 2 of the unrolled kernel, part 3: dword and qword memory updates -/


theorem setWidth8_xor_shr (x y : BitVec 64) (n : Nat) :
    ((x ^^^ y) >>> n).setWidth 8 = (x >>> n).setWidth 8 ^^^ (y >>> n).setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_xor, hi]

theorem wr64_xor (M : Mem) (a : Nat) (v : BitVec 64) : wr64 M a (rd64 M a ^^^ v) = xorQword M a v := by
  funext x
  by_cases hw : a ≤ x ∧ x < a + 8
  · obtain ⟨j, hj, rfl⟩ : ∃ j, j < 8 ∧ x = a + j := ⟨x - a, by omega, by omega⟩
    have hb : (rd64 M a >>> (8 * j)).setWidth 8 = M (a + j) := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and]
      exact getLsbD_rd64 M a j i hj hi
    have e : a + j - a = j := by omega
    simp only [xorQword, if_pos hw, e]
    rw [← hb, ← setWidth8_xor_shr]
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [wr64, wr8]
  · simp only [xorQword, if_neg hw]
    have h0 : x ≠ a := by omega
    have h1 : x ≠ a + 1 := by omega
    have h2 : x ≠ a + 2 := by omega
    have h3 : x ≠ a + 3 := by omega
    have h4 : x ≠ a + 4 := by omega
    have h5 : x ≠ a + 5 := by omega
    have h6 : x ≠ a + 6 := by omega
    have h7 : x ≠ a + 7 := by omega
    simp [wr64, wr8, h0, h1, h2, h3, h4, h5, h6, h7]

theorem rd32_byte (M : Mem) (a j : Nat) (hj : j < 4) : (rd32 M a >>> (8 * j)).setWidth 8 = M (a + j) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, rd32, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [BitVec.getLsbD_of_ge]

theorem wr32_byte (M : Mem) (a : Nat) (v : BitVec 32) (j : Nat) (hj : j < 4) :
    wr32 M a v (a + j) = (v >>> (8 * j)).setWidth 8 := by
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> simp [wr32, wr8]

theorem wr32_outside (M : Mem) (a : Nat) (v : BitVec 32) (x : Nat) (h : x < a ∨ a + 4 ≤ x) : wr32 M a v x = M x := by
  have h0 : x ≠ a := by omega
  have h1 : x ≠ a + 1 := by omega
  have h2 : x ≠ a + 2 := by omega
  have h3 : x ≠ a + 3 := by omega
  simp [wr32, wr8, h0, h1, h2, h3]

theorem rd32_ext (M N : Mem) (a : Nat) (h : ∀ j, j < 4 → M (a + j) = N (a + j)) : rd32 M a = rd32 N a := by
  unfold rd32
  have h0 := h 0 (by omega)
  rw [Nat.add_zero] at h0
  rw [h0, h 1 (by omega), h 2 (by omega), h 3 (by omega)]

theorem rd32_wr32 (M : Mem) (a : Nat) (v : BitVec 32) : rd32 (wr32 M a v) a = v := by
  have b0 := wr32_byte M a v 0 (by omega)
  have b1 := wr32_byte M a v 1 (by omega)
  have b2 := wr32_byte M a v 2 (by omega)
  have b3 := wr32_byte M a v 3 (by omega)
  rw [Nat.add_zero] at b0
  unfold rd32
  rw [b0, b1, b2, b3]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hi,
    decide_true, Bool.true_and]
  rcases (by omega : i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨ (24 ≤ i ∧ i < 32)) with h | h | h | h
  · have a1 : i < 16 := by omega
    have a2 : i < 24 := by omega
    simp [h, a1, a2]
  · have a1 : i < 16 := by omega
    have a2 : i < 24 := by omega
    have a3 : ¬ i < 8 := by omega
    have e : 8 + (i - 8) = i := by omega
    have c1 : i - 8 < 8 := by omega
    have c0 : i - 8 < 32 := by omega
    simp [a1, a2, a3, e, c1, c0]
  · have a1 : ¬ i < 16 := by omega
    have a2 : i < 24 := by omega
    have a3 : ¬ i < 8 := by omega
    have e : 16 + (i - 16) = i := by omega
    have e2 : 8 + (i - 8) = i := by omega
    have c1 : ¬ i - 8 < 8 := by omega
    have c2 : i - 16 < 8 := by omega
    have c0 : i - 8 < 32 := by omega
    have c00 : i - 16 < 32 := by omega
    simp [a1, a2, a3, e, e2, c1, c2, c0, c00]
  · have a1 : ¬ i < 16 := by omega
    have a2 : ¬ i < 24 := by omega
    have a3 : ¬ i < 8 := by omega
    have e : 24 + (i - 24) = i := by omega
    have e1 : 8 + (i - 8) = i := by omega
    have e2 : 16 + (i - 16) = i := by omega
    have c1 : ¬ i - 8 < 8 := by omega
    have c2 : ¬ i - 16 < 8 := by omega
    have c3 : i - 24 < 8 := by omega
    have c0 : i - 8 < 32 := by omega
    have c00 : i - 16 < 32 := by omega
    have c000 : i - 24 < 32 := by omega
    simp [a1, a2, a3, e, e1, e2, c1, c2, c3, c0, c00, c000]

theorem wr32_rd32 (M : Mem) (a : Nat) : wr32 M a (rd32 M a) = M := by
  funext x
  by_cases hw : a ≤ x ∧ x < a + 4
  · obtain ⟨j, hj, rfl⟩ : ∃ j, j < 4 ∧ x = a + j := ⟨x - a, by omega, by omega⟩
    rw [wr32_byte M a _ j hj, rd32_byte M a j hj]
  · exact wr32_outside M a _ x (by omega)

theorem wr32_wr32 (M : Mem) (a : Nat) (v w : BitVec 32) : wr32 (wr32 M a v) a w = wr32 M a w := by
  funext x
  by_cases hw : a ≤ x ∧ x < a + 4
  · obtain ⟨j, hj, rfl⟩ : ∃ j, j < 4 ∧ x = a + j := ⟨x - a, by omega, by omega⟩
    rw [wr32_byte _ a _ j hj, wr32_byte _ a _ j hj]
  · rw [wr32_outside _ a _ x (by omega), wr32_outside _ a _ x (by omega), wr32_outside _ a _ x (by omega)]


theorem rd32_xorQword_out (M : Mem) (ea : Nat) (v : BitVec 64) (a : Nat) (h : ea + 8 ≤ a ∨ a + 4 ≤ ea) :
    rd32 (xorQword M ea v) a = rd32 M a := by
  apply rd32_ext
  intro j hj
  unfold xorQword
  have : ¬ (ea ≤ a + j ∧ a + j < ea + 8) := by omega
  rw [if_neg this]

/-- The three memory effects of the self-modifying termination patch (`add dword [d], esi; xor qword [d'], rdi;
sub dword [d], esi`) are those of one `xorQword` at the patch address, when the patch lies outside the displacement field. -/
theorem patch_mem (M : Mem) (a ea : Nat) (c : BitVec 32) (v : BitVec 64) (h : ea + 8 ≤ a ∨ a + 4 ≤ ea) :
    wr32 (wr64 (wr32 M a (rd32 M a + c)) ea (rd64 (wr32 M a (rd32 M a + c)) ea ^^^ v)) a
      (rd32 (wr64 (wr32 M a (rd32 M a + c)) ea (rd64 (wr32 M a (rd32 M a + c)) ea ^^^ v)) a - c) = xorQword M ea v := by
  rw [wr64_xor, rd32_xorQword_out _ _ _ _ h, rd32_wr32, BitVec.add_sub_cancel]
  funext x
  by_cases hw : a ≤ x ∧ x < a + 4
  · obtain ⟨j, hj, rfl⟩ : ∃ j, j < 4 ∧ x = a + j := ⟨x - a, by omega, by omega⟩
    rw [wr32_byte _ a _ j hj, rd32_byte M a j hj]
    unfold xorQword
    have : ¬ (ea ≤ a + j ∧ a + j < ea + 8) := by omega
    rw [if_neg this]
  · rw [wr32_outside _ a _ x (by omega)]
    unfold xorQword
    by_cases hx : ea ≤ x ∧ x < ea + 8
    · rw [if_pos hx, if_pos hx, wr32_outside _ a _ x (by omega)]
    · rw [if_neg hx, if_neg hx, wr32_outside _ a _ x (by omega)]

end SmcTamper
