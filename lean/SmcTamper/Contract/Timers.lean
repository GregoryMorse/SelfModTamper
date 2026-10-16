module

@[expose] public section

namespace SmcTamper

/-! ## Timer contract (platform contract item 3, C08)

A timer is a counter with resolution `r > 0` and an unknown phase `φ`; a reading of the interval `[s, e)` is
`⌊(e + φ)/r⌋ − ⌊(s + φ)/r⌋`. -/

def reading (r φ s e : Nat) : Nat := (e + φ) / r - (s + φ) / r

/-- A reading of an interval of length `d` is `⌊d/r⌋` or `⌊d/r⌋ + 1`. -/
theorem reading_bounds (r φ s d : Nat) (hr : 0 < r) :
    d / r ≤ reading r φ s (s + d) ∧ reading r φ s (s + d) ≤ d / r + 1 := by
  unfold reading
  have h : ((s + φ) + d) / r = (s + φ) / r + d / r + if r ≤ (s + φ) % r + d % r then 1 else 0 := Nat.add_div hr
  have e : s + d + φ = (s + φ) + d := by omega
  rw [e, h]
  generalize d / r = q
  generalize (s + φ) / r = p
  split <;> omega

/-- **C08 (resolution).**  Intervals whose lengths differ by less than the resolution can be indistinguishable: for
`d₁ ≤ d₂ < d₁ + r` there is a phase giving the same reading. -/
theorem reading_indistinguishable (r s d1 d2 : Nat) (hr : 0 < r) (h12 : d1 ≤ d2) (h : d2 < d1 + r) :
    ∃ φ, reading r φ s (s + d1) = reading r φ s (s + d2) := by
  refine ⟨(r - (s + d1) % r) % r, ?_⟩
  unfold reading
  have key : ∃ m, (s + d1) + (r - (s + d1) % r) % r = r * m := by
    have h1 := Nat.div_add_mod (s + d1) r
    have h2 := Nat.mod_lt (s + d1) hr
    by_cases h0 : (s + d1) % r = 0
    · refine ⟨(s + d1) / r, ?_⟩
      rw [h0]; simp only [Nat.sub_zero, Nat.mod_self, Nat.add_zero]
      omega
    · refine ⟨(s + d1) / r + 1, ?_⟩
      rw [Nat.mod_eq_of_lt (by omega : r - (s + d1) % r < r), Nat.mul_add]
      omega
  obtain ⟨m, e1⟩ := key
  have hk : (r - (s + d1) % r) % r < r := Nat.mod_lt _ hr
  have e2 : s + d2 + (r - (s + d1) % r) % r = r * m + (d2 - d1) := by omega
  rw [e1, e2, Nat.mul_add_div hr, Nat.div_eq_of_lt (by omega : d2 - d1 < r), Nat.mul_div_cancel_left _ hr]
  simp

/-- FD observation O1 (Tables 4–5): every `Interrupt Time` minimum is at least `2.8806 ms` (`28806` units of `100 ns`) and a
timer of resolution `1 ms` (`10000` units) reads at least `2` on such an interval; the printed `Multimedia` minimum `1` therefore
cannot come from the same runs under this contract.  Recorded as an observation, not an erratum. -/
theorem multimedia_min_inconsistent (φ s d : Nat) (hd : 28806 ≤ d) : 2 ≤ reading 10000 φ s (s + d) := by
  have := (reading_bounds 10000 φ s d (by decide)).1
  omega

end SmcTamper
