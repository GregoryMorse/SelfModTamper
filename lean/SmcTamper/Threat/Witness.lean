module
public import SmcTamper.Threat.Security

@[expose] public section

namespace SmcTamper

/-! ## Non-vacuity: the hypotheses of T1 are jointly satisfiable

A concrete system (one unit, honest checks only, no writes) satisfies the well-formedness conditions and A1–A8 at Level L0 with
the inline timer.  This shows the hypothesis set is consistent; it does not say the system is secure against anything beyond T1. -/

def wSys : Sys where
  I0 := fun _ => 0
  n := 1
  unit := fun _ => ⟨⟨64, 0, 8, 0x13⟩, fun _ => False, fun _ => False, 1, 1⟩
  prot := fun _ => False
  ops := fun _ => False
  k := 2

def wCost : Cost := ⟨fun _ => 2, 1, 1⟩

def wTl : Nat → TEv := fun _ => TEv.check 0 .honest 1 1

def wSch : Sched wSys.n wTl where
  ck := fun _ m => m
  incr := fun _ m => Nat.lt_succ_self m
  isChk := fun x _ h => by
    have : x = 0 := by simp [wSys] at h; omega
    subst this; exact ⟨.honest, 1, 1, rfl⟩
  complete := by
    intro i x p e r h _
    exact ⟨i, rfl⟩

theorem wWorld (n : Nat) : worldAt wSys wTl n = World.init wSys := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [worldAt, ih]; rfl

theorem wWF : WF wSys wCost .L0 .tsc wTl where
  lvl := by
    intro i
    simp [wTl, Level.allows]
  cost := by
    intro i
    simp [wTl, Cost.admits, wSys]
  honestCode := by
    intro i x e r h a hc
    exact absurd hc (by simp [wSys])
  neutralMod := by
    intro i x e r h
    simp [wTl] at h
  medSplit := by
    intro i x med e r h
    simp [wTl] at h

theorem wAssumptions : Assumptions wSys wCost wTl wSch where
  a1 := by intro n; rw [wWorld]; rfl
  a2cov := by intro a h; exact absurd h (by simp [wSys])
  a2code := by intro x _ a h; exact absurd h (by simp [wSys])
  a2conn := by
    intro x y hx hy
    have hx0 : x = 0 := by simp [wSys] at hx; omega
    have hy0 : y = 0 := by simp [wSys] at hy; omega
    subst hx0; subst hy0
    exact Reach.refl hx
  a2intact := ⟨0, by simp [wSys], by
    intro ⟨i, a, b, h, _⟩
    simp [wTl] at h⟩
  a3 := by intro x _; simp [wSys, wCost]
  a4 := by intro i a b; simp [wTl]
  a5 := by intro i x p e r h; simp [wTl] at h; omega
  a6 := by intro i a b x m0 h; simp [wTl] at h
  a7 := by intro x _ a h; exact absurd h (by simp [wSys])
  a8 := by
    intro x m e r _ _ ⟨a, _, _, h⟩
    rw [wWorld] at h
    exact absurd rfl h

/-- Consistency check: the security theorem applies to the witness (the conclusion is not about an inconsistent set). -/
theorem witness_secure : ¬ Wins wSys wTl wSch := security wSys wCost .L0 .tsc wTl wSch wWF wAssumptions

end SmcTamper
