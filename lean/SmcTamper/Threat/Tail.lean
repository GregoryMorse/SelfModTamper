module
public import SmcTamper.Threat.Levels

@[expose] public section

namespace SmcTamper

/-! ## Scaffold for the necessity witnesses (T3)

A single-unit system `mkSys` (a unit with region `[0, size)`, code `[0, c)`, protected `[0, p)`) and timelines `tailTl pre N chk`: a
prefix of `N` events followed by the same check event forever.  The checks of the unit are exactly the indices `N + m`. -/

def mkSys (I0 : Mem) (op size : Nat) (canon : BitVec 8) (c p tau native k : Nat) : Sys where
  I0 := I0
  n := 1
  unit := fun _ => ⟨⟨op, 0, size, canon⟩, fun a => a < c, fun a => a = 0, tau, native⟩
  prot := fun a => a < p
  ops := fun _ => False
  k := k

def tailTl (pre : Nat → TEv) (N : Nat) (chk : TEv) : Nat → TEv := fun i => if i < N then pre i else chk

theorem tailTl_pre (pre : Nat → TEv) (N : Nat) (chk : TEv) {i : Nat} (h : i < N) : tailTl pre N chk i = pre i := by
  simp [tailTl, h]

theorem tailTl_tail (pre : Nat → TEv) (N : Nat) (chk : TEv) (m : Nat) : tailTl pre N chk (N + m) = chk := by
  have : ¬ (N + m < N) := by omega
  simp [tailTl, this]

def tailSch (S : Sys) (hn : S.n = 1) (pre : Nat → TEv) (N : Nat) (p : CheckPath) (e r : Nat)
    (hpre : ∀ i, i < N → ∀ x p e r, pre i ≠ TEv.check x p e r) : Sched S.n (tailTl pre N (TEv.check 0 p e r)) where
  ck := fun _ m => N + m
  incr := fun _ m => by omega
  isChk := fun x m hx => by
    have hx0 : x = 0 := by omega
    subst hx0
    exact ⟨p, e, r, tailTl_tail pre N _ m⟩
  complete := by
    intro i x p' e' r' h hx
    by_cases hi : i < N
    · rw [tailTl_pre pre N _ hi] at h
      exact absurd h (hpre i hi x p' e' r')
    · refine ⟨i - N, by omega⟩

theorem tail_world (S : Sys) (pre : Nat → TEv) (N : Nat) (x : Nat) (p : CheckPath) (e r : Nat) (m : Nat) :
    worldAt S (tailTl pre N (TEv.check x p e r)) (N + m) = worldAt S (tailTl pre N (TEv.check x p e r)) N := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have : worldAt S (tailTl pre N (TEv.check x p e r)) (N + (m + 1)) =
        stepW (worldAt S (tailTl pre N (TEv.check x p e r)) (N + m)) (tailTl pre N (TEv.check x p e r) (N + m)) := rfl
    rw [this, tailTl_tail, ih]
    rfl

/-! ### Generic facts about `mkSys` -/

section Mk
variable (I0 : Mem) (op size : Nat) (canon : BitVec 8) (c p tau native k : Nat)

theorem mk_inRegion (a : Nat) : (mkSys I0 op size canon c p tau native k).inRegion 0 a ↔ a < 8 * (size / 8) := by
  simp [Sys.inRegion, mkSys]

theorem mk_cov (hp : p ≤ 8 * (size / 8)) : A2cov (mkSys I0 op size canon c p tau native k) := by
  intro a ha
  refine ⟨0, by simp [mkSys], ?_⟩
  rw [mk_inRegion]
  simp [mkSys] at ha
  omega

theorem mk_code (hc : c ≤ p) : A2code (mkSys I0 op size canon c p tau native k) := by
  intro x _ a ha
  simp [mkSys] at ha ⊢
  omega

theorem mk_conn : A2conn (mkSys I0 op size canon c p tau native k) := by
  intro x y hx hy
  have hx0 : x = 0 := by simp [mkSys] at hx; omega
  have hy0 : y = 0 := by simp [mkSys] at hy; omega
  subst hx0; subst hy0
  exact Reach.refl hx

theorem mk_resp (hc : 0 < c) : A7 (mkSys I0 op size canon c p tau native k) := by
  intro x _ a ha
  simp [mkSys] at ha ⊢
  omega

end Mk

/-- Generic: a modification of a byte outside every unit's code leaves the unit intact. -/
theorem intact_of_writes (S : Sys) (tl : Nat → TEv) (v : Nat)
    (h : ∀ i a b, tl i = TEv.write a b → ¬ (S.unit v).code a) : Intact S tl v := by
  intro ⟨i, a, b, hw, hc, _, _⟩
  exact h i a b hw hc

/-! ### Generic facts about tail timelines -/

section Tl
variable (S : Sys) (pre : Nat → TEv) (N : Nat) (p : CheckPath) (e r : Nat)

theorem tail_a1 (hns : ∀ i, i < N → ∀ a b, pre i ≠ TEv.splitWrite a b) :
    A1 S (tailTl pre N (TEv.check 0 p e r)) := by
  have key : ∀ n, (worldAt S (tailTl pre N (TEv.check 0 p e r)) n).split = false := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [worldAt]
      by_cases hi : n < N
      · rw [tailTl_pre pre N _ hi]
        cases e : pre n with
        | splitWrite a b => exact absurd e (hns n hi a b)
        | _ => simp only [stepW]; exact ih
      · rw [show tailTl pre N (TEv.check 0 p e r) n = TEv.check 0 p e r by simp [tailTl, hi]]
        simp only [stepW]; exact ih
  exact key

theorem tail_a4 (hnd : ∀ i, i < N → ∀ a b, pre i ≠ TEv.dmaWrite a b) : A4 (tailTl pre N (TEv.check 0 p e r)) := by
  intro i a b h
  by_cases hi : i < N
  · rw [tailTl_pre pre N _ hi] at h; exact hnd i hi a b h
  · simp [tailTl, hi] at h

theorem tail_a5 (hr : r = e) (hnc : ∀ i, i < N → ∀ x p e r, pre i ≠ TEv.check x p e r) :
    A5 (tailTl pre N (TEv.check 0 p e r)) := by
  intro i x p' e' r' h
  by_cases hi : i < N
  · rw [tailTl_pre pre N _ hi] at h; exact absurd h (hnc i hi x p' e' r')
  · simp [tailTl, hi] at h
    obtain ⟨_, _, h2, h3⟩ := h
    omega

/-- No alarm: the tail checks pass in value and are within the threshold. -/
theorem tail_noalarm (hn : S.n = 1) (hk : 0 < S.k) (hnc : ∀ i, i < N → ∀ x p e r, pre i ≠ TEv.check x p e r)
    (hok : checkOk S (worldAt S (tailTl pre N (TEv.check 0 p e r)) N) 0 p) (hr : ¬ (S.unit 0).tau < r) :
    ¬ Alarm S (tailTl pre N (TEv.check 0 p e r)) (tailSch S hn pre N p e r hnc) := by
  intro ⟨x, hx, _, h⟩
  have hx0 : x = 0 := by omega
  subst hx0
  rcases h with ⟨m, c, e', r', hc, hnot⟩ | ⟨s, hs⟩
  · simp only [tailSch] at hc hnot
    rw [tailTl_tail] at hc
    simp only [TEv.check.injEq] at hc
    obtain ⟨_, rfl, _, _⟩ := hc
    apply hnot
    rw [tail_world]
    exact hok
  · obtain ⟨c, e', r', hc, hlt⟩ := hs 0 hk
    simp only [tailSch] at hc
    rw [Nat.add_zero, tailTl_tail] at hc
    simp only [TEv.check.injEq] at hc
    obtain ⟨_, _, _, rfl⟩ := hc
    exact hr hlt

/-- Every index past the prefix sees the world after the prefix. -/
theorem tail_world_ge (i : Nat) (h : N ≤ i) :
    worldAt S (tailTl pre N (TEv.check 0 p e r)) i = worldAt S (tailTl pre N (TEv.check 0 p e r)) N := by
  obtain ⟨m, rfl⟩ : ∃ m, i = N + m := ⟨i - N, by omega⟩
  exact tail_world S pre N 0 p e r m

theorem tail_wf (C : Cost) (l : Level) (t : TimerSrc)
    (hpl : ∀ i, i < N → l.allows t (tailTl pre N (TEv.check 0 p e r)) i (pre i))
    (hcl : ∀ i, l.allows t (tailTl pre N (TEv.check 0 p e r)) i (TEv.check 0 p e r))
    (hpc : ∀ i, i < N → C.admits S (pre i)) (hcc : C.admits S (TEv.check 0 p e r))
    (hnc : ∀ i, i < N → ∀ x p e r, pre i ≠ TEv.check x p e r)
    (hh : p = .honest → ∀ a, (S.unit 0).code a → ¬ S.ops a → (worldAt S (tailTl pre N (TEv.check 0 p e r)) N).F a = S.I0 a)
    (hn' : p = .neutral → ∃ a, (S.unit 0).code a ∧ ¬ S.ops a ∧ (worldAt S (tailTl pre N (TEv.check 0 p e r)) N).F a ≠ S.I0 a)
    (hm : ∀ med, p = .mediated med → (worldAt S (tailTl pre N (TEv.check 0 p e r)) N).split = true) :
    WF S C l t (tailTl pre N (TEv.check 0 p e r)) where
  lvl := by
    intro i
    by_cases hi : i < N
    · rw [tailTl_pre pre N _ hi]; exact hpl i hi
    · rw [show tailTl pre N (TEv.check 0 p e r) i = TEv.check 0 p e r by simp [tailTl, hi]]; exact hcl i
  cost := by
    intro i
    by_cases hi : i < N
    · rw [tailTl_pre pre N _ hi]; exact hpc i hi
    · rw [show tailTl pre N (TEv.check 0 p e r) i = TEv.check 0 p e r by simp [tailTl, hi]]; exact hcc
  honestCode := by
    intro i x e' r' h
    by_cases hi : i < N
    · rw [tailTl_pre pre N _ hi] at h; exact absurd h (hnc i hi x _ e' r')
    · simp only [tailTl, hi, ite_false, TEv.check.injEq] at h
      obtain ⟨hx, hp, _, _⟩ := h
      subst hx
      rw [tail_world_ge S pre N p e r i (by omega)]
      exact hh hp
  neutralMod := by
    intro i x e' r' h
    by_cases hi : i < N
    · rw [tailTl_pre pre N _ hi] at h; exact absurd h (hnc i hi x _ e' r')
    · simp only [tailTl, hi, ite_false, TEv.check.injEq] at h
      obtain ⟨hx, hp, _, _⟩ := h
      subst hx
      rw [tail_world_ge S pre N p e r i (by omega)]
      exact hn' hp
  medSplit := by
    intro i x med e' r' h
    by_cases hi : i < N
    · rw [tailTl_pre pre N _ hi] at h; exact absurd h (hnc i hi x _ e' r')
    · simp only [tailTl, hi, ite_false, TEv.check.injEq] at h
      obtain ⟨_, hp, _, _⟩ := h
      rw [tail_world_ge S pre N p e r i (by omega)]
      exact hm med hp

theorem tail_intact (v : Nat) (hv : v = 0)
    (hw : ∀ i, i < N → ∀ a b, pre i = TEv.write a b → ¬ (S.unit v).code a) :
    Intact S (tailTl pre N (TEv.check 0 p e r)) v := by
  apply intact_of_writes
  intro i a b h
  by_cases hi : i < N
  · rw [tailTl_pre pre N _ hi] at h; exact hw i hi a b h
  · simp [tailTl, hi] at h

theorem tail_a6 (hn : S.n = 1) (hnc : ∀ i, i < N → ∀ x p e r, pre i ≠ TEv.check x p e r)
    (hper : ∀ i, i < N → ∀ a b, pre i = TEv.write a b → S.prot a → b ≠ S.I0 a →
      (worldAt S (tailTl pre N (TEv.check 0 p e r)) N).D a ≠ S.I0 a) :
    A6 S (tailTl pre N (TEv.check 0 p e r)) (tailSch S hn pre N p e r hnc) := by
  intro i a b x m0 hw hprot _ hb _ _ _ _ j _
  have hi : i < N := by
    refine Classical.byContradiction (fun h => ?_)
    simp [tailTl, h] at hw
  rw [tailTl_pre pre N _ hi] at hw
  simp only [tailSch]
  rw [tail_world]
  exact hper i hi a b hw hprot hb

theorem tail_exec (j a : Nat) (hj : j < N) (hx : pre j = TEv.exec a) (hprot : S.prot a) (hops : ¬ S.ops a)
    (hF : (worldAt S (tailTl pre N (TEv.check 0 p e r)) j).F a ≠ S.I0 a) :
    ExecViolation S (tailTl pre N (TEv.check 0 p e r)) :=
  ⟨j, a, by rw [tailTl_pre pre N _ hj]; exact hx, hprot, hops, hF⟩

end Tl

/-! ### Prefix from a list -/

def preSeq (l : List TEv) : Nat → TEv := fun i => l.getD i TEv.idle

theorem preSeq_mem (l : List TEv) (i : Nat) (h : i < l.length) : preSeq l i ∈ l := by
  simp only [preSeq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  exact List.getElem_mem h

end SmcTamper
