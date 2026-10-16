module
public import SmcTamper.Threat.Witnesses3

@[expose] public section

namespace SmcTamper

/-! ## T3 (necessity)

For each of A1, A2 (coverage), A2 (an intact unit), A3, A4, A5, A6, A8 there is a concrete system and timeline that satisfies the
well-formedness conditions and every other assumption, in which the adversary wins; hence, by T1, the dropped assumption is
false there.  Not covered by a witness (open obligations, `lean/PAPER_MAP.md`): A2 `code ⊆ prot` and strong connectivity of the covers
graph (needs a two-unit system), and A7 (the response-code coverage; it plays the role of making a unit's alarm effective, and the
neutralise-all witness of A2 is the closest case). -/

/-- The packaged statement of necessity of one assumption. -/
def Necessary (i : Nat) : Prop :=
  ∃ (S : Sys) (C : Cost) (l : Level) (t : TimerSrc) (tl : Nat → TEv) (sch : Sched S.n tl),
    WF S C l t tl ∧ AllBut i S C tl sch ∧ Wins S tl sch ∧ ¬ Holds i S C tl sch

theorem necessary_of (i : Nat) (hi : i = 1 ∨ i = 2 ∨ i = 12 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 8)
    (S : Sys) (C : Cost) (l : Level) (t : TimerSrc) (tl : Nat → TEv) (sch : Sched S.n tl)
    (hwf : WF S C l t tl) (hall : AllBut i S C tl sch) (hw : Wins S tl sch) : Necessary i :=
  ⟨S, C, l, t, tl, sch, hwf, hall, hw, not_holds S C l t tl sch hwf hw i hi hall⟩

theorem necessary_A1 : Necessary 1 := by
  obtain ⟨C, sch, h1, h2, h3⟩ := nec_A1; exact necessary_of 1 (by omega) _ _ _ _ _ _ h1 h2 h3
theorem necessary_A2cov : Necessary 2 := by
  obtain ⟨C, sch, h1, h2, h3⟩ := nec_A2cov; exact necessary_of 2 (by omega) _ _ _ _ _ _ h1 h2 h3
theorem necessary_A2intact : Necessary 12 := by
  obtain ⟨C, sch, h1, h2, h3⟩ := nec_A2intact; exact necessary_of 12 (by omega) _ _ _ _ _ _ h1 h2 h3
theorem necessary_A3 : Necessary 3 := by
  obtain ⟨C, sch, h1, h2, h3, _⟩ := nec_A3; exact necessary_of 3 (by omega) _ _ _ _ _ _ h1 h2 h3
theorem necessary_A4 : Necessary 4 := by
  obtain ⟨C, sch, h1, h2, h3⟩ := nec_A4; exact necessary_of 4 (by omega) _ _ _ _ _ _ h1 h2 h3
theorem necessary_A5 : Necessary 5 := by
  obtain ⟨C, sch, h1, h2, h3, _⟩ := nec_A5; exact necessary_of 5 (by omega) _ _ _ _ _ _ h1 h2 h3
theorem necessary_A6 : Necessary 6 := by
  obtain ⟨C, sch, h1, h2, h3⟩ := nec_A6; exact necessary_of 6 (by omega) _ _ _ _ _ _ h1 h2 h3
theorem necessary_A8 : Necessary 8 := by
  obtain ⟨C, sch, h1, h2, h3⟩ := nec_A8; exact necessary_of 8 (by omega) _ _ _ _ _ _ h1 h2 h3

/-- **T3.**  Each of the listed assumptions is necessary for T1. -/
theorem T3 : Necessary 1 ∧ Necessary 2 ∧ Necessary 12 ∧ Necessary 3 ∧ Necessary 4 ∧ Necessary 5 ∧ Necessary 6 ∧ Necessary 8 :=
  ⟨necessary_A1, necessary_A2cov, necessary_A2intact, necessary_A3, necessary_A4, necessary_A5, necessary_A6, necessary_A8⟩

end SmcTamper
