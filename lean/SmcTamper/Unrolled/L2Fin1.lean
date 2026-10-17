module
public import SmcTamper.Unrolled.L2Post

@[expose] public section

namespace SmcTamper

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Level 2 of the unrolled kernel, part 11: the patched unit and the memory it leaves behind -/

theorem toInt_ofNat32 (n : Nat) (h : n < 2147483648) : (BitVec.ofNat 32 n).toInt = n := by
  have : BitVec.ofNat 32 n = sdisp (n : Int) := by unfold sdisp; simp
  rw [this]; exact toInt_sdisp _ (by omega) (by omega)

theorem unitsFrom_snoc (base : Nat) : ∀ (n u : Nat) (k : KState), u < numUnits →
    unitsFrom base u (n + 1) k = unitStep base ((u + n) % numUnits) (unitsFrom base u n k) := by
  intro n
  induction n with
  | zero => intro u k hu; simp [unitsFrom, Nat.mod_eq_of_lt hu]
  | succ n ih =>
    intro u k hu
    have hu' : (u + 1) % numUnits < numUnits := Nat.mod_lt _ (by rw [numUnits_296]; omega)
    have e : ((u + 1) % numUnits + n) % numUnits = (u + (n + 1)) % numUnits := by rw [numUnits_296]; omega
    show unitsFrom base ((u + 1) % numUnits) (n + 1) (unitStep base u k) =
      unitStep base ((u + (n + 1)) % numUnits) (unitsFrom base ((u + 1) % numUnits) n (unitStep base u k))
    rw [ih _ _ hu', e]

theorem unitsFrom_mem_out (base x : Nat) (hx : ∀ v, v < 296 → x ≠ base + opOff v) :
    ∀ (n u : Nat) (k : KState), (unitsFrom base u n k).mem x = k.mem x := by
  intro n
  induction n with
  | zero => intro u k; rfl
  | succ n ih =>
    intro u k
    show (unitsFrom base ((u + 1) % numUnits) n (unitStep base u k)).mem x = _
    rw [ih]
    have ht : (u + perPage) % numUnits < 296 := by rw [numUnits_296]; omega
    have := hx _ ht
    unfold unitStep
    dsimp only
    simp only [wr8, this, if_false]

theorem imgOk_mono (enc : Instr → List Nat) (base : Nat) (M : Mem) (E E' : Nat → Prop) (h : ImgOk enc base M E)
    (hs : ∀ i, E i → E' i) : ImgOk enc base M E' :=
  fun i hi hop hn => h i hi hop (fun e => hn (hs i e))

/-- The five bytes of unit `w`'s `LEA` and the first byte after it, in the image. -/
theorem lea_orig (enc : Instr → List Nat) (henc : EncOk enc) (base : Nat) (M : Mem) (E : Nat → Prop)
    (hI : ImgOk enc base M E) (w : Nat) (hw : w ≤ 294) (h147 : w ≠ 147) (hE : ∀ j, j < 5 → ¬ E (leaOff w + j)) :
    ∀ j, j < 5 → (M (base + leaOff w + j)).toNat = [0x48, 0x8D, 0x49, 0x08, 0x48].getD j 0 := by
  intro j hj
  have hs := rsiOf_spec w
  have hs1 := rsiOf_spec (w + 1)
  have hl : ∀ o, leaOff w + o = unitStart w + (23 + o) := by intro o; simp only [leaOff]; omega
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl
  · rw [show base + leaOff w + 0 = base + (unitStart w + 23) by simp only [leaOff]; omega,
      unit_byte enc base M E hI w 23 (by omega) (by omega) (by omega) (by have := hE 0 (by omega); rwa [hl] at this)]
    rcases henc with rfl | rfl <;> rfl
  · rw [show base + leaOff w + 1 = base + (unitStart w + 24) by simp only [leaOff]; omega,
      unit_byte enc base M E hI w 24 (by omega) (by omega) (by omega) (by have := hE 1 (by omega); rwa [hl] at this)]
    rcases henc with rfl | rfl <;> rfl
  · rw [show base + leaOff w + 2 = base + (unitStart w + 25) by simp only [leaOff]; omega,
      unit_byte enc base M E hI w 25 (by omega) (by omega) (by omega) (by have := hE 2 (by omega); rwa [hl] at this)]
    rcases henc with rfl | rfl <;> rfl
  · rw [show base + leaOff w + 3 = base + (unitStart w + 26) by simp only [leaOff]; omega,
      unit_byte enc base M E hI w 26 (by omega) (by omega) (by omega) (by have := hE 3 (by omega); rwa [hl] at this)]
    rcases henc with rfl | rfl <;> rfl
  · have e : unitStart (w + 1) = unitStart w + 27 := by simp only [unitStart, introLen]; omega
    have hE4 := hE 4 (by omega)
    have e2 : leaOff w + 4 = unitStart (w + 1) + 0 := by simp only [leaOff]; omega
    rw [e2] at hE4
    rw [show base + leaOff w + 4 = base + (unitStart (w + 1) + 0) by rw [← e2]; omega,
      unit_byte enc base M E hI (w + 1) 0 (by omega) (by omega) (by omega) hE4]
    rcases henc with rfl | rfl <;> rfl

theorem patchVal_xor (w : Nat) :
    patchVal (w + 1) = 0x4808498D48#64 ^^^ (0xE9#64 ||| ((BitVec.ofNat 32 (patchImm - rsiOf w)).setWidth 64 <<< 8)) := by
  have h := patch_xor (BitVec.ofNat 32 (patchImm - rsiOf w))
  have e : patchVal (w + 1) = patchMask (BitVec.ofNat 32 (patchImm - rsiOf w)) := by
    unfold patchVal; rw [Nat.add_sub_cancel]
  rw [e, ← h, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem orig_byte (j : Nat) (hj : j < 5) (b : BitVec 8) (hb : b.toNat = [0x48, 0x8D, 0x49, 0x08, 0x48].getD j 0) :
    b = (0x4808498D48#64 >>> (8 * j)).setWidth 8 := by
  apply BitVec.eq_of_toNat_eq
  rw [hb]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl <;> decide +kernel

/-- After the patch, the five bytes are `E9 disp32`. -/
theorem patched_bytes (M : Mem) (a w : Nat)
    (ho : ∀ j, j < 5 → (M (a + j)).toNat = [0x48, 0x8D, 0x49, 0x08, 0x48].getD j 0) :
    bytesAt (xorQword M a (patchVal (w + 1))) a 5 = encode (.jmp32 (BitVec.ofNat 32 (patchImm - rsiOf w))) := by
  have hb : ∀ k, k < (encode (.jmp32 (BitVec.ofNat 32 (patchImm - rsiOf w)))).length →
      ((xorQword M a (patchVal (w + 1))) (a + k)).toNat = (encode (.jmp32 (BitVec.ofNat 32 (patchImm - rsiOf w)))).getD k 0 := by
    intro k hk
    have hk5 : k < 5 := by simpa [encode, bytes32] using hk
    have hx : xorQword M a (patchVal (w + 1)) (a + k) = (M (a + k)) ^^^ ((patchVal (w + 1)) >>> (8 * k)).setWidth 8 := by
      unfold xorQword; rw [if_pos (by omega), Nat.add_sub_cancel_left]
    rw [hx, orig_byte k hk5 _ (ho k hk5), patchVal_xor, ← setWidth8_xor_shr, ← BitVec.xor_assoc,
      BitVec.xor_self, BitVec.zero_xor]
    generalize BitVec.ofNat 32 (patchImm - rsiOf w) = dd
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) with rfl | rfl | rfl | rfl | rfl
    · simp only [Nat.mul_zero, BitVec.ushiftRight_zero]
      rw [jw_byte0]; rfl
    · have h1 := jw_byte dd 0 (by omega)
      simp only [Nat.zero_add] at h1
      rw [Nat.mul_one, h1]
      simp [encode, bytes32, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    · have h1 := jw_byte dd 1 (by omega)
      rw [show 8 * 2 = 8 * (1 + 1) from rfl, h1]
      simp [encode, bytes32, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    · have h1 := jw_byte dd 2 (by omega)
      rw [show 8 * 3 = 8 * (2 + 1) from rfl, h1]
      simp [encode, bytes32, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    · have h1 := jw_byte dd 3 (by omega)
      rw [show 8 * 4 = 8 * (3 + 1) from rfl, h1]
      simp [encode, bytes32, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := bytesAt_eq_of _ a _ hb
  simpa [encode, bytes32] using this

end SmcTamper
