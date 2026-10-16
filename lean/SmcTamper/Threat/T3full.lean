module
public import SmcTamper.Threat.Witnesses5

@[expose] public section

namespace SmcTamper

/-! ## T3 for all eleven assumptions

`T3` (Threat/T3) covers A1, A2 coverage, A2 intact unit, A3, A4, A5, A6, A8.  Here A7 (response coverage), A2 code protected and A2
strong connectivity (two units), so that every assumption field has a necessity witness: a concrete system and timeline that satisfies
the well-formedness conditions and all other assumptions, in which the adversary wins. -/

def Necessary3 (i : Nat) : Prop :=
  ∃ (S : Sys) (C : Cost) (l : Level) (t : TimerSrc) (tl : Nat → TEv) (sch : Sched S.n tl),
    WF S C l t tl ∧ AllBut3 i S C tl sch ∧ Wins S tl sch ∧ ¬ Holds3 i S

theorem necessary_A7 : Necessary3 7 := by
  obtain ⟨C, sch, h1, h2, h3, h4⟩ := nec_A7; exact ⟨_, C, _, _, _, sch, h1, h2, h3, h4⟩
theorem necessary_A2code : Necessary3 13 := by
  obtain ⟨C, sch, h1, h2, h3, h4⟩ := nec_A2code; exact ⟨_, C, _, _, _, sch, h1, h2, h3, h4⟩
theorem necessary_A2conn : Necessary3 14 := by
  obtain ⟨C, sch, h1, h2, h3, h4⟩ := nec_A2conn; exact ⟨_, C, _, _, _, sch, h1, h2, h3, h4⟩

/-- **T3 (all assumptions).**  Each of A1, A2 (coverage, code protected, connectivity, an intact unit), A3, A4, A5, A6, A7, A8 is
necessary for T1. -/
theorem T3_full :
    (Necessary 1 ∧ Necessary 2 ∧ Necessary 12 ∧ Necessary 3 ∧ Necessary 4 ∧ Necessary 5 ∧ Necessary 6 ∧ Necessary 8) ∧
    Necessary3 7 ∧ Necessary3 13 ∧ Necessary3 14 :=
  ⟨T3, necessary_A7, necessary_A2code, necessary_A2conn⟩

end SmcTamper
