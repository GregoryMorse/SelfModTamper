module
public import SmcTamper.Threat.Witness

@[expose] public section

namespace SmcTamper

/-! ## What the levels give

Adversary levels below L2 with an inline timer (L0, L1 + `tsc`) imply the structural assumptions A1, A4, A5 from the level
well-formedness `WF.lvl`; they are consequences, not extra assumptions. -/

theorem lvl_a4 {S : Sys} {C : Cost} {l : Level} {t : TimerSrc} {tl : Nat → TEv} (hwf : WF S C l t tl) (h : l.rank < 4) :
    ∀ i a b, tl i ≠ TEv.dmaWrite a b := by
  intro i a b e
  have := hwf.lvl i
  rw [e] at this
  simp only [Level.allows] at this
  omega

theorem lvl_a5 {S : Sys} {C : Cost} {l : Level} {t : TimerSrc} {tl : Nat → TEv} (hwf : WF S C l t tl)
    (h : ¬ l.forgesReading t) : ∀ i x p e r, tl i = TEv.check x p e r → r = e := by
  intro i x p e r ev
  have := hwf.lvl i
  rw [ev] at this
  simp only [Level.allows] at this
  rcases this.1 with h1 | h1
  · exact h1
  · exact absurd h1 h

theorem lvl_a1 {S : Sys} {C : Cost} {l : Level} {t : TimerSrc} {tl : Nat → TEv} (hwf : WF S C l t tl) (h : l.rank < 2) :
    ∀ n, (worldAt S tl n).split = false := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [worldAt]
    have hl := hwf.lvl n
    cases e : tl n with
    | splitWrite a b => rw [e] at hl; simp only [Level.allows] at hl; omega
    | write a b => simp only [stepW]; exact ih
    | dmaWrite a b => simp only [stepW]; exact ih
    | exec _ => simp only [stepW]; exact ih
    | check _ _ _ _ => simp only [stepW]; exact ih
    | regWrite => simp only [stepW]; exact ih
    | idle => simp only [stepW]; exact ih

/-- With the inline timer, an adversary at L0 or L1 cannot forge readings, split the views or write physically. -/
theorem tsc_low_level (S : Sys) (C : Cost) (l : Level) (tl : Nat → TEv) (hwf : WF S C l .tsc tl) (h : l.rank < 2) :
    (∀ n, (worldAt S tl n).split = false) ∧ (∀ i a b, tl i ≠ TEv.dmaWrite a b) ∧
      (∀ i x p e r, tl i = TEv.check x p e r → r = e) :=
  ⟨lvl_a1 hwf h, lvl_a4 hwf (by omega), lvl_a5 hwf (by simp only [Level.forgesReading]; omega)⟩

end SmcTamper
