module
public import SmcTamper.Threat.Timeline

@[expose] public section

namespace SmcTamper

theorem Reach.bound_right {S : Sys} {x y : Nat} (h : Reach S x y) : y < S.n := by
  cases h with
  | refl hx => exact hx
  | step _ hz _ => exact hz

/-- **Closure.**  With a path in the covers graph from an intact unit `v`, any modified unit `u` has a modification that lies in
the region of an intact unit: some intact unit `y` covers a byte `c` that a write modified, and `c` is a code byte of a unit
`u'`. -/
theorem closure_detect (S : Sys) (tl : Nat → TEv) (v : Nat) (hv : Intact S tl v) :
    ∀ u, Reach S v u → ModWrite S tl u →
      ∃ y u' i c b, y < S.n ∧ u' < S.n ∧ Intact S tl y ∧ tl i = TEv.write c b ∧ ¬ S.ops c ∧ b ≠ S.I0 c ∧
        S.inRegion y c ∧ (S.unit u').code c := by
  intro u hr
  induction hr with
  | refl hx => intro hm; exact absurd hm hv
  | @step w z hxw hz hcov ih =>
    intro hm
    by_cases hmw : ModWrite S tl w
    · exact ih hmw
    · obtain ⟨i, a, b, hw, hc, ho, hb⟩ := hm
      exact ⟨w, z, i, a, b, hxw.bound_right, hz, hmw, hw, ho, hb, hcov a hc ho, hc⟩

end SmcTamper
