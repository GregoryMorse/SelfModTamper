module
public import SmcTamper.Spec.Images
public import SmcTamper.Spec.Step
public import SmcTamper.Layout.Numbers

@[expose] public section

namespace SmcTamper

/-! ## Where the displacements point (C27, C29) -/

theorem toInt_sdisp (z : Int) (h1 : -2147483648 ≤ z) (h2 : z < 2147483648) : (sdisp z).toInt = z := by
  unfold sdisp
  rw [BitVec.toInt_ofInt]
  exact Int.bmod_eq_of_le (by simp; omega) (by simp; omega)

/-- C27: the `XOR BYTE PTR [rip+d], DL` of unit `u` addresses the opcode byte of unit `(u + 148) mod 296`, i.e. the unit
at the same position in the other page. The address is computed by the semantics (`ripEA`) from the displacement stored
in the instruction. -/
theorem unit_xor_target (u : Nat) (hu : u < numUnits) :
    ripEA (unitStart u + 17) 6 (unitDisp u) = opOff ((u + perPage) % numUnits) := by
  have hp : perPage = 148 := perPage_148
  have hn : numUnits = 296 := numUnits_296
  have h1 := rsiOf_spec u
  have h2 := rsiOf_spec ((u + perPage) % numUnits)
  simp only [hp, hn] at h2 hu
  have hd : (unitDisp u).toInt = (opOff ((u + perPage) % numUnits) : Int) - ((unitStart u + 23 : Nat) : Int) := by
    unfold unitDisp
    apply toInt_sdisp <;>
    · simp only [opOff, unitStart, introLen, hp, hn]; omega
  unfold ripEA
  rw [hd]
  simp only [Int.ofNat_eq_natCast, opOff, unitStart, introLen, hp, hn] at *
  omega

/-- The XOR's target is never the unit's own opcode byte and always lies in the other page. -/
theorem unit_xor_other_page (u : Nat) (hu : u < numUnits) :
    (u < perPage ↔ perPage ≤ (u + perPage) % numUnits) := by
  have hp : perPage = 148 := perPage_148
  have hn : numUnits = 296 := numUnits_296
  simp only [hp, hn] at hu ⊢; omega

end SmcTamper
