module
public import SmcTamper.Threat.Tail

@[expose] public section

namespace SmcTamper

/-! ## T3 (necessity): for each assumption a timeline that satisfies all the others and wins

Each witness is a tail timeline (`Tail`): a prefix followed by one check event forever.  `AllBut i` says that every assumption
except the one numbered `i` holds (1 A1, 2 A2 coverage, 12 A2 one intact unit, 3 A3, 4 A4, 5 A5, 6 A6, 8 A8), so "the others hold"
is checked, not claimed.  By T1 the dropped assumption is then false for the witness (`not_of_wins`). -/

def AllBut (i : Nat) (S : Sys) (C : Cost) (tl : Nat → TEv) (sch : Sched S.n tl) : Prop :=
  (i = 1 ∨ A1 S tl) ∧ (i = 2 ∨ A2cov S) ∧ A2code S ∧ A2conn S ∧ (i = 12 ∨ A2intact S tl) ∧ (i = 3 ∨ A3 S C) ∧
  (i = 4 ∨ A4 tl) ∧ (i = 5 ∨ A5 tl) ∧ (i = 6 ∨ A6 S tl sch) ∧ A7 S ∧ (i = 8 ∨ A8 S tl sch)

/-- The dropped assumption, by number. -/
def Holds : Nat → (S : Sys) → Cost → (tl : Nat → TEv) → Sched S.n tl → Prop
  | 1, S, _, tl, _ => A1 S tl
  | 2, S, _, _, _ => A2cov S
  | 12, S, _, tl, _ => A2intact S tl
  | 3, S, C, _, _ => A3 S C
  | 4, _, _, tl, _ => A4 tl
  | 5, _, _, tl, _ => A5 tl
  | 6, S, _, tl, sch => A6 S tl sch
  | 8, S, _, tl, sch => A8 S tl sch
  | _, _, _, _, _ => True

/-- If everything but assumption `i` holds and the adversary wins, then assumption `i` fails (T1 contrapositive). -/
theorem not_holds (S : Sys) (C : Cost) (l : Level) (t : TimerSrc) (tl : Nat → TEv) (sch : Sched S.n tl)
    (hwf : WF S C l t tl) (hw : Wins S tl sch) (i : Nat) (hi : i = 1 ∨ i = 2 ∨ i = 12 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 8)
    (h : AllBut i S C tl sch) : ¬ Holds i S C tl sch := by
  intro hH
  obtain ⟨h1, h2, h2c, h2n, h12, h3, h4, h5, h6, h7, h8⟩ := h
  apply security S C l t tl sch hwf _ hw
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  refine ⟨?_, ?_, h2c, h2n, ?_, ?_, ?_, ?_, ?_, h7, ?_⟩ <;>
  first
    | exact hH
    | exact h1.resolve_left (by decide)
    | exact h2.resolve_left (by decide)
    | exact h12.resolve_left (by decide)
    | exact h3.resolve_left (by decide)
    | exact h4.resolve_left (by decide)
    | exact h5.resolve_left (by decide)
    | exact h6.resolve_left (by decide)
    | exact h8.resolve_left (by decide)

end SmcTamper
