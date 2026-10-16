module

@[expose] public section

namespace SmcTamper

/-- **P05 (overhead).**  If a common additive overhead `o ≥ 0` (a console write, a counter read) is inside both timed intervals
then the measured ratio is not larger than the true one: `(a + o) / (b + o) ≤ a / b` when `b ≤ a`, cross-multiplied. -/
theorem overhead_conservative (a b o : Nat) (hab : b ≤ a) : (a + o) * b ≤ a * (b + o) := by
  rw [Nat.add_mul, Nat.mul_add]
  have := Nat.mul_le_mul_left o hab
  rw [Nat.mul_comm o a] at this
  omega

end SmcTamper
