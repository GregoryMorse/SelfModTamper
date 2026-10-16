module
public import SmcTamper.Threat.Witnesses4

@[expose] public section

namespace SmcTamper

/-! ## Scaffold for two-unit witnesses: a prefix followed by a body of four events repeated forever

`loopTl pre N b0 b1 b2 b3` is the timeline whose events before `N` are `pre` and whose event `N + 4 m + j` is `b_j`. -/

def bAt (b0 b1 b2 b3 : TEv) (j : Nat) : TEv := if j = 0 then b0 else if j = 1 then b1 else if j = 2 then b2 else b3

def loopTl (pre : Nat → TEv) (N : Nat) (b0 b1 b2 b3 : TEv) : Nat → TEv :=
  fun i => if i < N then pre i else bAt b0 b1 b2 b3 ((i - N) % 4)

section Loop
variable (pre : Nat → TEv) (N : Nat) (b0 b1 b2 b3 : TEv)

theorem loopTl_pre {i : Nat} (h : i < N) : loopTl pre N b0 b1 b2 b3 i = pre i := by simp [loopTl, h]

theorem loopTl_body {i : Nat} (h : N ≤ i) : loopTl pre N b0 b1 b2 b3 i = bAt b0 b1 b2 b3 ((i - N) % 4) := by
  have : ¬ i < N := by omega
  simp [loopTl, this]

theorem loop_prop (P : TEv → Prop) (hpre : ∀ i, i < N → P (pre i)) (h0 : P b0) (h1 : P b1) (h2 : P b2) (h3 : P b3) :
    ∀ i, P (loopTl pre N b0 b1 b2 b3 i) := by
  intro i
  by_cases hi : i < N
  · rw [loopTl_pre pre N b0 b1 b2 b3 hi]; exact hpre i hi
  · rw [loopTl_body pre N b0 b1 b2 b3 (by omega)]
    have : (i - N) % 4 = 0 ∨ (i - N) % 4 = 1 ∨ (i - N) % 4 = 2 ∨ (i - N) % 4 = 3 := by omega
    rcases this with h | h | h | h <;> rw [h] <;> simpa [bAt]

/-- The world at step `j` of a period. -/
def loopW (W0 : World) : Nat → World
  | 0 => W0
  | 1 => stepW W0 b0
  | 2 => stepW (stepW W0 b0) b1
  | _ => stepW (stepW (stepW W0 b0) b1) b2

theorem loop_world_mod (S : Sys)
    (hper : stepW (stepW (stepW (stepW (worldAt S (loopTl pre N b0 b1 b2 b3) N) b0) b1) b2) b3 =
      worldAt S (loopTl pre N b0 b1 b2 b3) N) :
    ∀ i, N ≤ i → worldAt S (loopTl pre N b0 b1 b2 b3) i =
      loopW b0 b1 b2 (worldAt S (loopTl pre N b0 b1 b2 b3) N) ((i - N) % 4) := by
  intro i hi
  obtain ⟨m, rfl⟩ : ∃ m, i = N + m := ⟨i - N, by omega⟩
  induction m with
  | zero => simp [loopW]
  | succ m ih =>
    have hi' : N ≤ N + m := by omega
    have ih := ih hi'
    have e : worldAt S (loopTl pre N b0 b1 b2 b3) (N + m + 1) =
        stepW (worldAt S (loopTl pre N b0 b1 b2 b3) (N + m)) (loopTl pre N b0 b1 b2 b3 (N + m)) := rfl
    rw [show N + (m + 1) = N + m + 1 by omega, e, ih, loopTl_body pre N b0 b1 b2 b3 hi']
    have h4 : (N + m + 1 - N) % 4 = ((N + m - N) % 4 + 1) % 4 := by omega
    rw [h4]
    have : (N + m - N) % 4 = 0 ∨ (N + m - N) % 4 = 1 ∨ (N + m - N) % 4 = 2 ∨ (N + m - N) % 4 = 3 := by omega
    rcases this with h | h | h | h <;> rw [h] <;> simp [loopW, bAt, hper]

/-- A schedule for two units, the checks of unit `x` being the events `N + 4 m + pos x`. -/
def loopSch (S : Sys) (hn : S.n = 2) (pos : Nat → Nat) (hpos : ∀ x, x < 2 → pos x < 4)
    (hchk : ∀ x, x < 2 → ∃ p e r, bAt b0 b1 b2 b3 (pos x) = TEv.check x p e r)
    (hone : ∀ j, j < 4 → ∀ x p e r, bAt b0 b1 b2 b3 j = TEv.check x p e r → x < 2 → j = pos x)
    (hpre : ∀ i, i < N → ∀ x p e r, pre i ≠ TEv.check x p e r) : Sched S.n (loopTl pre N b0 b1 b2 b3) where
  ck := fun x m => N + 4 * m + pos x
  incr := fun x m => by omega
  isChk := fun x m hx => by
    obtain ⟨p, e, r, h⟩ := hchk x (by omega)
    refine ⟨p, e, r, ?_⟩
    rw [loopTl_body pre N b0 b1 b2 b3 (by omega)]
    have : (N + 4 * m + pos x - N) % 4 = pos x := by have := hpos x (by omega); omega
    rw [this]; exact h
  complete := by
    intro i x p e r h hx
    by_cases hi : i < N
    · rw [loopTl_pre pre N b0 b1 b2 b3 hi] at h
      exact absurd h (hpre i hi x p e r)
    · rw [loopTl_body pre N b0 b1 b2 b3 (by omega)] at h
      have hj := hone ((i - N) % 4) (by omega) x p e r h (by omega)
      exact ⟨(i - N) / 4, by omega⟩

theorem loop_a1 (S : Sys) (h : ∀ i a b, loopTl pre N b0 b1 b2 b3 i ≠ TEv.splitWrite a b) :
    A1 S (loopTl pre N b0 b1 b2 b3) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [worldAt]
    cases e : loopTl pre N b0 b1 b2 b3 n with
    | splitWrite a b => exact absurd e (h n a b)
    | _ => simp only [stepW]; exact ih

end Loop

/-! ### Two units -/

def du0 : CUnit := ⟨⟨64, 0, 0, 0x13⟩, fun a => a < 8, fun a => a = 0, 1, 1⟩

/-- Unit 0 has region `[0, s0)` and code `[0, 8)`; unit 1 has region `[st1, st1 + s1)` and code `[16, 24)`; the image is all zero. -/
def duoSys (prot : Nat → Prop) (s0 st1 s1 : Nat) : Sys where
  I0 := fun _ => 0
  n := 2
  unit := fun x => if x = 0 then ⟨⟨64, 0, s0, 0x13⟩, fun a => a < 8, fun a => a = 0, 1, 1⟩
    else ⟨⟨65, st1, s1, 0x13⟩, fun a => 16 ≤ a ∧ a < 24, fun a => a = 16, 1, 1⟩
  prot := prot
  ops := fun _ => False
  k := 2

theorem duo_inRegion0 (prot : Nat → Prop) (s0 st1 s1 a : Nat) :
    (duoSys prot s0 st1 s1).inRegion 0 a ↔ a < 8 * (s0 / 8) := by
  simp [Sys.inRegion, duoSys]

theorem duo_inRegion1 (prot : Nat → Prop) (s0 st1 s1 a : Nat) :
    (duoSys prot s0 st1 s1).inRegion 1 a ↔ st1 ≤ a ∧ a < st1 + 8 * (s1 / 8) := by
  simp [Sys.inRegion, duoSys]

theorem duo_A3 (prot : Nat → Prop) (s0 st1 s1 : Nat) : A3 (duoSys prot s0 st1 s1) ⟨fun _ => 2, 2, 2⟩ := by
  intro x hx
  by_cases h : x = 0 <;> simp [duoSys, h]

end SmcTamper
