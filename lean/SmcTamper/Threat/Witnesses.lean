module
public import SmcTamper.Threat.Necessity

@[expose] public section

namespace SmcTamper

/-! ## Witnesses for T3, part 1: emulation-based (A3 and A5) -/

theorem preSeq_prop (L : List TEv) (P : TEv → Prop) (hL : ∀ e ∈ L, P e) : ∀ i, i < L.length → P (preSeq L i) :=
  fun i hi => hL _ (preSeq_mem L i hi)

/-- The base system: region `[0,16)`, code `[0,8)`, protected `[0,16)`, `tau = native = 1`, `k = 2`, all bytes zero. -/
def zSys : Sys := mkSys (fun _ => 0) 64 16 0x13 8 16 1 1 2

/-- Modify byte 8 (protected, outside every unit's code), then execute it. -/
def zL : List TEv := [TEv.write 8 1, TEv.exec 8]

theorem zL_nc : ∀ i, i < zL.length → ∀ x p e r, preSeq zL i ≠ TEv.check x p e r :=
  fun i hi x p e r => preSeq_prop zL (fun ev => ev ≠ TEv.check x p e r) (by simp [zL]) i hi
theorem zL_ns : ∀ i, i < zL.length → ∀ a b, preSeq zL i ≠ TEv.splitWrite a b :=
  fun i hi a b => preSeq_prop zL (fun ev => ev ≠ TEv.splitWrite a b) (by simp [zL]) i hi
theorem zL_nd : ∀ i, i < zL.length → ∀ a b, preSeq zL i ≠ TEv.dmaWrite a b :=
  fun i hi a b => preSeq_prop zL (fun ev => ev ≠ TEv.dmaWrite a b) (by simp [zL]) i hi

abbrev zTlE (e r : Nat) : Nat → TEv := tailTl (preSeq zL) zL.length (TEv.check 0 .emulated e r)

def zSchE (e r : Nat) : Sched zSys.n (zTlE e r) := tailSch zSys rfl (preSeq zL) zL.length .emulated e r zL_nc

theorem zE_world (e r : Nat) : worldAt zSys (zTlE e r) zL.length = ⟨wr8 (fun _ => 0) 8 1, wr8 (fun _ => 0) 8 1, false⟩ := by
  simp [zTlE, worldAt, stepW, tailTl, preSeq, zL, World.init, zSys, mkSys]

theorem zE_core (C : Cost) (l : Level) (t : TimerSrc) (e r : Nat) (hl : 1 ≤ l.rank) (hfr : r = e ∨ l.forgesReading t)
    (hc : C.emulLB 0 ≤ e) (hr : r ≤ 1) :
    WF zSys C l t (zTlE e r) ∧ A1 zSys (zTlE e r) ∧ A2cov zSys ∧ A2code zSys ∧ A2conn zSys ∧ A2intact zSys (zTlE e r) ∧
      A4 (zTlE e r) ∧ A6 zSys (zTlE e r) (zSchE e r) ∧ A7 zSys ∧ A8 zSys (zTlE e r) (zSchE e r) ∧
      Wins zSys (zTlE e r) (zSchE e r) := by
  have hI : ∀ a, zSys.I0 a = 0 := fun _ => rfl
  refine ⟨?_, tail_a1 _ _ _ _ _ _ zL_ns, mk_cov _ _ _ _ _ _ _ _ _ (by decide), mk_code _ _ _ _ _ _ _ _ _ (by decide),
    mk_conn _ _ _ _ _ _ _ _ _, ⟨0, by decide, tail_intact _ _ _ _ _ _ 0 rfl ?_⟩, tail_a4 _ _ _ _ _ zL_nd,
    tail_a6 _ _ _ _ _ _ rfl (by decide) zL_nc ?_, mk_resp _ _ _ _ _ _ _ _ _ (by decide), ?_, ?_⟩
  · refine tail_wf _ _ _ _ _ _ C l t ?_ ?_ ?_ ?_ zL_nc (by simp) (by simp) (by simp)
    · intro i hi
      have := preSeq_prop zL (fun ev => l.allows t (zTlE e r) i ev) ?_ i hi
      · exact this
      · intro ev hev
        simp only [zL, List.mem_cons, List.not_mem_nil, or_false] at hev
        rcases hev with rfl | rfl <;> simp [Level.allows] <;> omega
    · intro i
      simp only [Level.allows]
      exact ⟨hfr, hl⟩
    · intro i hi
      exact preSeq_prop zL (fun ev => C.admits zSys ev) (by simp [zL, Cost.admits]) i hi
    · simp only [Cost.admits]; simpa [zSys, mkSys] using hc
  · intro i hi a b hw
    have : preSeq zL i ∈ zL := preSeq_mem zL i hi
    rw [hw] at this
    simp only [zL, List.mem_cons, List.not_mem_nil, or_false, TEv.write.injEq, reduceCtorEq] at this
    obtain ⟨rfl, rfl⟩ := this
    simp [zSys, mkSys]
  · intro i hi a b hw _ _
    have : preSeq zL i ∈ zL := preSeq_mem zL i hi
    rw [hw] at this
    simp only [zL, List.mem_cons, List.not_mem_nil, or_false, TEv.write.injEq, reduceCtorEq] at this
    obtain ⟨rfl, rfl⟩ := this
    rw [zE_world]
    simp [wr8, zSys, mkSys]
  · intro x m e' r' _ h
    simp only [zSchE, tailSch, zTlE] at h
    rw [tailTl_tail] at h
    simp at h
  · refine ⟨tail_exec _ _ _ _ _ _ 1 8 (by simp [zL]) (by simp [preSeq, zL]) (by simp [zSys, mkSys]) (by simp [zSys, mkSys]) ?_,
      tail_noalarm zSys _ _ _ _ _ rfl (by decide) zL_nc (by simp [checkOk]) (by simp [zSys, mkSys]; omega)⟩
    have : worldAt zSys (zTlE e r) 1 = ⟨wr8 (fun _ => 0) 8 1, wr8 (fun _ => 0) 8 1, false⟩ := by
      simp [zTlE, worldAt, stepW, tailTl, preSeq, zL, World.init, zSys, mkSys]
    rw [this]
    simp [wr8, zSys, mkSys]

/-- **T3, A3.**  With an emulation lower bound of `0` (the calibration condition fails), emulated checks are accepted:
the adversary executes modified bytes and no alarm is raised. -/
theorem nec_A3 : ∃ (C : Cost) (sch : Sched zSys.n (zTlE 1 1)),
    WF zSys C .L1 .tsc (zTlE 1 1) ∧ AllBut 3 zSys C (zTlE 1 1) sch ∧ Wins zSys (zTlE 1 1) sch ∧ ¬ A3 zSys C := by
  obtain ⟨hwf, h1, h2, h2c, h2n, h12, h4, h6, h7, h8, hw⟩ :=
    zE_core ⟨fun _ => 0, 1, 1⟩ .L1 .tsc 1 1 (by decide) (Or.inl rfl) (by decide) (by decide)
  have h5 : A5 (zTlE 1 1) := tail_a5 _ _ _ _ _ rfl zL_nc
  refine ⟨⟨fun _ => 0, 1, 1⟩, zSchE 1 1, hwf, ?_, hw, ?_⟩
  · exact ⟨Or.inr h1, Or.inr h2, h2c, h2n, Or.inr h12, Or.inl rfl, Or.inr h4, Or.inr h5, Or.inr h6, h7, Or.inr h8⟩
  · intro h
    have := (h 0 (by decide)).2.1
    simp [zSys, mkSys] at this

/-- **T3, A5.**  With adversary-chosen readings (an L2 capability), replaying a native reading passes while a slow emulation runs:
the elapsed time is `100`, the reading `1`. -/
theorem nec_A5 : ∃ (C : Cost) (sch : Sched zSys.n (zTlE 100 1)),
    WF zSys C .L2 .tsc (zTlE 100 1) ∧ AllBut 5 zSys C (zTlE 100 1) sch ∧ Wins zSys (zTlE 100 1) sch ∧ ¬ A5 (zTlE 100 1) := by
  obtain ⟨hwf, h1, h2, h2c, h2n, h12, h4, h6, h7, h8, hw⟩ :=
    zE_core ⟨fun _ => 2, 1, 1⟩ .L2 .tsc 100 1 (by decide) (Or.inr (by simp [Level.forgesReading, Level.rank])) (by decide) (by decide)
  have h3 : A3 zSys ⟨fun _ => 2, 1, 1⟩ := by intro x hx; simp [zSys, mkSys]
  refine ⟨⟨fun _ => 2, 1, 1⟩, zSchE 100 1, hwf, ?_, hw, ?_⟩
  · exact ⟨Or.inr h1, Or.inr h2, h2c, h2n, Or.inr h12, Or.inr h3, Or.inr h4, Or.inl rfl, Or.inr h6, h7, Or.inr h8⟩
  · intro h
    have := h (zL.length) 0 .emulated 100 1 (by simp [zTlE, tailTl])
    omega

end SmcTamper
