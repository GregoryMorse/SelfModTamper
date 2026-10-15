module
public import SmcTamper.Spec.Bits

public section

namespace SmcTamper

/-- The paper's C `paritybyte` returns the odd-parity bit, so its negation is the x86 parity flag (R2, C19). -/
theorem paritybyteC_eq_not_evenParity8 : ∀ v : BitVec 8, paritybyteC v = !evenParity8 v := by
  decide +revert

/-- `!paritybyte((unsigned char)res)` of Fig. 3 is the parity flag of the result. -/
theorem not_paritybyteC_eq_pf (res : BitVec 64) : (!paritybyteC (res.setWidth 8)) = pf res := by
  rw [paritybyteC_eq_not_evenParity8]; simp [pf]

end SmcTamper
