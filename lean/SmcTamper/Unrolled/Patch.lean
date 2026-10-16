module
public import SmcTamper.Unrolled.Emulation

@[expose] public section

namespace SmcTamper

set_option linter.unusedVariables false

/-! ## The termination patch touches five bytes: the `LEA` and the next byte, never an opcode byte -/

theorem patchMask_high (disp : BitVec 32) (k : Nat) (hk : 40 ≤ k) : (patchMask disp).getLsbD k = false := by
  unfold patchMask
  rw [patchMask_const, BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft]
  have h1 : (0x4808498DA1#64).getLsbD k = false := const_bit_false 0x4808498DA1 40 k (by decide) hk
  have h2 : (disp.setWidth 64).getLsbD (k - 8) = false := by
    rw [BitVec.getLsbD_setWidth]
    have : disp.getLsbD (k - 8) = false := BitVec.getLsbD_of_ge disp (k - 8) (by omega)
    simp [this]
  simp [h1, h2]

theorem patchVal_high (n j : Nat) (h5 : 5 ≤ j) (h8 : j < 8) : maskByte (patchVal n) j = 0 := by
  unfold maskByte patchVal
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_zero]
  have := patchMask_high (BitVec.ofNat 32 (patchImm - rsiOf (n - 1))) (8 * j + i) (by omega)
  simp [this]

/-- The patch bytes are never an opcode byte of any unit: unit `u`'s opcode is one byte after its start, the patch bytes
lie in `leaOff (n-1) .. leaOff (n-1) + 4`. -/
theorem patch_not_opcode (n w j : Nat) (hn : 1 ≤ n) (hn' : n ≤ 296) (hw : w < 296) (hj : j < 5) :
    opOff w ≠ leaOff (n - 1) + j := by
  have h1 := rsiOf_spec w
  have h2 := rsiOf_spec (n - 1)
  simp only [opOff, leaOff, unitStart, introLen]
  omega

end SmcTamper
