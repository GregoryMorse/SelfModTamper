module
public import SmcTamper.Threat.T3

@[expose] public section

namespace SmcTamper

/-! ## Witnesses for T3, part 4: response coverage (A7), and the two-unit assumptions (A2 code, A2 connectivity)

`AllBut3 i` is `AllBut` for the assumptions numbered 7 (A7), 13 (A2: every unit's code is protected) and 14 (A2: the covers graph is
strongly connected): everything else holds.  `not_holds3` is T1 contrapositive for them. -/

def AllBut3 (i : Nat) (S : Sys) (C : Cost) (tl : Nat → TEv) (sch : Sched S.n tl) : Prop :=
  A1 S tl ∧ A2cov S ∧ (i = 13 ∨ A2code S) ∧ (i = 14 ∨ A2conn S) ∧ A2intact S tl ∧ A3 S C ∧ A4 tl ∧ A5 tl ∧ A6 S tl sch ∧
  (i = 7 ∨ A7 S) ∧ A8 S tl sch

def Holds3 : Nat → Sys → Prop
  | 7, S => A7 S
  | 13, S => A2code S
  | 14, S => A2conn S
  | _, _ => True

theorem not_holds3 (S : Sys) (C : Cost) (l : Level) (t : TimerSrc) (tl : Nat → TEv) (sch : Sched S.n tl)
    (hwf : WF S C l t tl) (hw : Wins S tl sch) (i : Nat) (hi : i = 7 ∨ i = 13 ∨ i = 14)
    (h : AllBut3 i S C tl sch) : ¬ Holds3 i S := by
  intro hH
  obtain ⟨h1, h2, h2c, h2n, h12, h3, h4, h5, h6, h7, h8⟩ := h
  apply security S C l t tl sch hwf _ hw
  rcases hi with rfl | rfl | rfl <;>
  refine ⟨h1, h2, ?_, ?_, h12, h3, h4, h5, h6, ?_, h8⟩ <;>
  first
    | exact hH
    | exact h2c.resolve_left (by decide)
    | exact h2n.resolve_left (by decide)
    | exact h7.resolve_left (by decide)

/-! ### A7: the response code lies outside the unit's own code, and the adversary modifies it

The unit has code `[0,8)` and its response byte at address 8 (protected, in the region, not part of the code).  The adversary modifies
and executes byte 8; every check is emulated (so it overruns the threshold), but the response code is not intact, so no alarm is
effective. -/

def mkSysR (I0 : Mem) (op size : Nat) (canon : BitVec 8) (c p tau native k rp : Nat) : Sys where
  I0 := I0
  n := 1
  unit := fun _ => ⟨⟨op, 0, size, canon⟩, fun a => a < c, fun a => a = rp, tau, native⟩
  prot := fun a => a < p
  ops := fun _ => False
  k := k

def rSys : Sys := mkSysR (fun _ => 0) 64 16 0x13 8 16 1 1 2 8

theorem rSys_cov : A2cov rSys := by
  intro a ha
  refine ⟨0, by simp [rSys, mkSysR], ?_⟩
  simp [rSys, mkSysR, Sys.inRegion] at ha ⊢
  omega

theorem rSys_code : A2code rSys := by
  intro x _ a ha
  simp [rSys, mkSysR] at ha ⊢
  omega

theorem rSys_conn : A2conn rSys := by
  intro x y hx hy
  have hx0 : x = 0 := by simp [rSys, mkSysR] at hx; omega
  have hy0 : y = 0 := by simp [rSys, mkSysR] at hy; omega
  subst hx0; subst hy0
  exact Reach.refl hx

abbrev rTl : Nat → TEv := tailTl (preSeq zL) zL.length (TEv.check 0 .emulated 5 5)

def rSch : Sched rSys.n rTl := tailSch rSys rfl (preSeq zL) zL.length .emulated 5 5 zL_nc

def rCost : Cost := ⟨fun _ => 5, 5, 5⟩

theorem nec_A7 : ∃ (C : Cost) (sch : Sched rSys.n rTl),
    WF rSys C .L1 .tsc rTl ∧ AllBut3 7 rSys C rTl sch ∧ Wins rSys rTl sch ∧ ¬ A7 rSys := by
  have hI : ∀ a, rSys.I0 a = 0 := fun _ => rfl
  have hW : worldAt rSys rTl zL.length = ⟨wr8 (fun _ => 0) 8 1, wr8 (fun _ => 0) 8 1, false⟩ := by
    simp [rTl, worldAt, stepW, tailTl, preSeq, zL, World.init, rSys, mkSysR]
  have hwf : WF rSys rCost .L1 .tsc rTl := by
    refine tail_wf _ _ _ _ _ _ rCost .L1 .tsc ?_ ?_ ?_ ?_ zL_nc (by simp) (by simp) (by simp)
    · intro i hi
      have := preSeq_prop zL (fun ev => Level.L1.allows .tsc rTl i ev) ?_ i hi
      · exact this
      · intro ev hev
        simp only [zL, List.mem_cons, List.not_mem_nil, or_false] at hev
        rcases hev with rfl | rfl <;> simp [Level.allows, Level.rank]
    · intro i
      simp [Level.allows, Level.rank]
    · intro i hi
      exact preSeq_prop zL (fun ev => rCost.admits rSys ev) (by simp [zL, Cost.admits]) i hi
    · simp [Cost.admits, rCost]
  have hA6 : A6 rSys rTl rSch := by
    refine tail_a6 _ _ _ _ _ _ rfl zL_nc ?_
    intro i hi a b h _ _
    have : preSeq zL i ∈ zL := preSeq_mem zL i hi
    rw [h] at this
    simp only [zL, List.mem_cons, List.not_mem_nil, or_false, TEv.write.injEq, reduceCtorEq] at this
    obtain ⟨rfl, rfl⟩ := this
    rw [hW]
    simp [wr8, rSys, mkSysR]
  have hnr : ¬ A7 rSys := by
    intro h
    have := (h 0 (by simp [rSys, mkSysR])) 8 (by simp [rSys, mkSysR])
    simp [rSys, mkSysR] at this
  refine ⟨rCost, rSch, hwf, ⟨tail_a1 _ _ _ _ _ _ zL_ns, rSys_cov, Or.inr rSys_code, Or.inr rSys_conn,
    ⟨0, by simp [rSys, mkSysR], tail_intact _ _ _ _ _ _ 0 rfl ?_⟩, ?_, tail_a4 _ _ _ _ _ zL_nd, tail_a5 _ _ _ _ _ rfl zL_nc, hA6,
    Or.inl rfl, ?_⟩, ⟨?_, ?_⟩, hnr⟩
  · intro i hi a b h
    have : preSeq zL i ∈ zL := preSeq_mem zL i hi
    rw [h] at this
    simp only [zL, List.mem_cons, List.not_mem_nil, or_false, TEv.write.injEq, reduceCtorEq] at this
    obtain ⟨rfl, rfl⟩ := this
    simp [rSys, mkSysR]
  · intro x hx; simp [rSys, mkSysR, rCost]
  · intro x m e' r' _ h
    simp only [rSch, tailSch, rTl] at h
    rw [tailTl_tail] at h
    simp at h
  · refine tail_exec _ _ _ _ _ _ 1 8 (by simp [zL]) (by simp [preSeq, zL]) (by simp [rSys, mkSysR]) (by simp [rSys, mkSysR]) ?_
    have : worldAt rSys rTl 1 = ⟨wr8 (fun _ => 0) 8 1, wr8 (fun _ => 0) 8 1, false⟩ := by
      simp [rTl, worldAt, stepW, tailTl, preSeq, zL, World.init, rSys, mkSysR]
    rw [this]
    simp [wr8, rSys, mkSysR]
  · rintro ⟨x, hx, hresp, _⟩
    have := hresp zL.length 8 (by simp [rSys, mkSysR])
    rw [hW] at this
    simp [wr8, rSys, mkSysR] at this

end SmcTamper
