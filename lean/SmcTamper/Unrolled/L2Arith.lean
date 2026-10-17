module
public import SmcTamper.Unrolled.L2Tab

@[expose] public section

namespace SmcTamper

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Level 2 of the unrolled kernel, part 8: bit-vector arithmetic of the intro and of the patch -/

theorem toNat_sub2368 (a : BitVec 64) (h : 2368 < a.toNat) : (a - 2368).toNat = a.toNat - 2368 := by
  rw [BitVec.toNat_sub]
  have : (2368 : BitVec 64).toNat = 2368 := by decide
  rw [this]
  omega

theorem shr_dec (R : BitVec 64) (h1 : 8 ≤ R.toNat) :
    (R >>> 3) - 1 = BitVec.ofNat 64 (R.toNat / 8 - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]
  have h2 := R.isLt
  have : (1 : BitVec 64).toNat = 1 := by decide
  rw [this]
  simp only [Nat.shiftRight_eq_div_pow]
  have h3 : R.toNat / 2 ^ 3 = R.toNat / 8 := rfl
  rw [h3]
  omega

theorem imul27 (m : Nat) (hm : m < 296) :
    BitVec.ofInt 64 ((BitVec.ofNat 64 m).toInt * (27 : BitVec 8).toInt) = BitVec.ofNat 64 (27 * m) := by
  have h27 : (27 : BitVec 8).toInt = 27 := by decide
  have hm' : (BitVec.ofNat 64 m).toInt = (m : Int) := by
    rw [BitVec.toInt_ofNat']
    apply Int.bmod_eq_of_le <;> omega
  rw [h27, hm', show (m : Int) * 27 = ((27 * m : Nat) : Int) by push_cast; omega, BitVec.ofInt_natCast]

theorem add32_5 (a : Nat) (h : a < 2 ^ 31) :
    (((BitVec.ofNat 64 a).setWidth 32 + (5 : BitVec 8).signExtend 32).setWidth 64) = BitVec.ofNat 64 (a + 5) := by
  apply BitVec.eq_of_toNat_eq
  have h5 : ((5 : BitVec 8).signExtend 32).toNat = 5 := by decide
  rw [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat, h5, BitVec.toNat_ofNat]
  have h6 : a % 2 ^ 64 = a := Nat.mod_eq_of_lt (by omega)
  rw [h6]
  have h7 : a % 2 ^ 32 = a := Nat.mod_eq_of_lt (by omega)
  rw [h7]
  omega

theorem ofNat_sub64 (a b : Nat) (h : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have h1 : a % 2 ^ 64 = a := Nat.mod_eq_of_lt ha
  have h2 : b % 2 ^ 64 = b := Nat.mod_eq_of_lt (by omega)
  have h3 : (a - b) % 2 ^ 64 = a - b := Nat.mod_eq_of_lt (by omega)
  rw [h1, h2, h3]
  omega

theorem sext7974 : (7974 : BitVec 32).signExtend 64 = 7974 := by decide +kernel

theorem xor_patch (v : Nat) (hv : v < 2 ^ 32) :
    BitVec.ofNat 64 0x4808498DA1 ^^^ (BitVec.ofNat 64 v <<< 8) = patchMask (BitVec.ofNat 32 v) := by
  unfold patchMask
  rw [patchMask_const]
  congr 2
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem rd32_of_bytes (M : Mem) (a : Nat) (d : BitVec 32) (h : ∀ j, j < 4 → (M (a + j)).toNat = (bytes32 d).getD j 0) :
    rd32 M a = d := by
  have e : rd32 M a = rd32 (wr32 (fun _ => 0) a d) a := by
    apply rd32_ext
    intro j hj
    apply BitVec.eq_of_toNat_eq
    rw [h j hj, wr32_bytes32 _ _ _ j hj]
  rw [e, rd32_wr32]


theorem jw_byte0 (dd : BitVec 32) : (0xE9#64 ||| (dd.setWidth 64 <<< 8)).setWidth 8 = 0xE9#8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and]
  have : ¬ (8 ≤ i) := by omega
  have h8 : decide (i < 8) = true := by simpa using hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp

theorem jw_byte (dd : BitVec 32) (j : Nat) (hj : j < 4) :
    ((0xE9#64 ||| (dd.setWidth 64 <<< 8)) >>> (8 * (j + 1))).setWidth 8 = (dd >>> (8 * j)).setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, hi,
    decide_true, Bool.true_and]
  have e0 : (0xE9#64).getLsbD (8 * (j + 1) + i) = false := const_bit_false 0xE9 8 _ (by decide) (by omega)
  have e1 : 8 * (j + 1) + i - 8 = 8 * j + i := by omega
  have e2 : 8 * (j + 1) + i < 64 := by omega
  have e3 : 8 ≤ 8 * (j + 1) + i := by omega
  have e0' : (233#64)[8 * (j + 1) + i] = false := by
    have := e0; rwa [BitVec.getLsbD_eq_getElem e2] at this
  have e4 : 8 * j + i < 64 := by omega
  have e5 : ¬ (8 * (j + 1) + i < 8) := by omega
  simp [e0, e0', e1, e2, e4, e5]

end SmcTamper
