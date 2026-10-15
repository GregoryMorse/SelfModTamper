module
public import SmcTamper.Spec.Bits
public import SmcTamper.Bits.Mask

public section

namespace SmcTamper

set_option linter.unusedVariables false

theorem getLsbD_rd64 (m : Mem) (a q r : Nat) (hq : q < 8) (hr : r < 8) :
    (rd64 m a).getLsbD (8 * q + r) = (m (a + q)).getLsbD r := by
  have h64 : 8 * q + r < 64 := by omega
  unfold rd64
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, h64, decide_true, Bool.true_and]
  rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [BitVec.getLsbD_of_ge]

theorem getLsbD_255 : ∀ r : Fin 8, (255#64).getLsbD r.1 = true := by decide

theorem getLsbD_setByte (x : BitVec 64) (j : Nat) (b : BitVec 8) (q r : Nat) (hq : q < 8) (hr : r < 8) :
    (setByte x j b).getLsbD (8 * q + r) = if q = j then b.getLsbD r else x.getLsbD (8 * q + r) := by
  have h64 : 8 * q + r < 64 := by omega
  unfold setByte
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth, h64, decide_true, Bool.true_and]
  rcases Nat.lt_trichotomy q j with h | rfl | h
  · have h1 : 8 * q + r < 8 * j := by omega
    simp [h1, Nat.ne_of_lt h]
  · have e : 8 * q + r - 8 * q = r := by omega
    have hr64 : r < 64 := by omega
    have h255' : (255#64).getLsbD r = true := by
      have := getLsbD_255 ⟨r, hr⟩; simpa using this
    have h255 : (255#64)[r] = true := by
      rw [← BitVec.getLsbD_eq_getElem]; exact h255'
    simp [e, hr, hr64, h255, h255', show ¬ (8 * q + r < 8 * q) by omega]
  · have h1 : ¬ 8 * q + r < 8 * j := by omega
    have c255 := const_bit_false 255 8 (8 * q + r - 8 * j) (by decide) (by omega)
    have cb : b.getLsbD (8 * q + r - 8 * j) = false := BitVec.getLsbD_of_ge _ _ (by omega)
    simp [h1, c255, cb, Nat.ne_of_gt h]

/-- A write outside the 8 bytes read leaves the 64-bit read unchanged. -/
theorem rd64_wr8_outside (m : Mem) (base a : Nat) (b : BitVec 8) (h : a < base ∨ base + 8 ≤ a) :
    rd64 (wr8 m a b) base = rd64 m base := by
  unfold rd64 wr8
  have : ∀ k, k < 8 → (base + k = a) = False := fun k hk => by
    apply eq_false; omega
  have h0 : ¬ base = a := by omega
  simp [h0, this 1 (by omega), this 2 (by omega), this 3 (by omega), this 4 (by omega),
    this 5 (by omega), this 6 (by omega), this 7 (by omega)] at *

/-- A write inside the 8 bytes read replaces exactly byte `a - base` (little-endian) of the word. -/
theorem rd64_wr8_inside (m : Mem) (base a : Nat) (b : BitVec 8) (h1 : base ≤ a) (h2 : a < base + 8) :
    rd64 (wr8 m a b) base = setByte (rd64 m base) (a - base) b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hq : i / 8 < 8 := by omega
  have hr : i % 8 < 8 := Nat.mod_lt _ (by omega)
  have hi' : i = 8 * (i / 8) + i % 8 := (Nat.div_add_mod i 8).symm
  rw [hi', getLsbD_rd64 _ _ _ _ hq hr, getLsbD_setByte _ _ _ _ _ hq hr, getLsbD_rd64 _ _ _ _ hq hr]
  unfold wr8
  by_cases hc : i / 8 = a - base
  · have : base + (a - base) = a := by omega
    simp [hc, this]
  · have : ¬ (base + i / 8 = a) := by omega
    simp [hc, this]

/-- The 8-aligned form used by the kernels: the qword containing byte `a`. -/
theorem rd64_wr8_aligned (m : Mem) (a : Nat) (b : BitVec 8) :
    rd64 (wr8 m a b) (a / 8 * 8) = setByte (rd64 m (a / 8 * 8)) (a % 8) b := by
  have := rd64_wr8_inside m (a / 8 * 8) a b (by omega) (by omega)
  rw [this]; congr 1; omega

/-- A write elsewhere does not change a byte. -/
theorem wr8_same (m : Mem) (a : Nat) (b : BitVec 8) : wr8 m a b a = b := by simp [wr8]
theorem wr8_other (m : Mem) (a x : Nat) (b : BitVec 8) (h : x ≠ a) : wr8 m a b x = m x := by simp [wr8, h]

end SmcTamper
