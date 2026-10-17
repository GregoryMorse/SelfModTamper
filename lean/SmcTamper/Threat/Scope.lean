module
public import SmcTamper.Threat.Matrix

@[expose] public section

namespace SmcTamper

/-! ## Scope of T1 (P12): what the goal does not cover -/

/-- Register writes, idle steps and executions do not change the memory views: register tampering is not modelled as a goal. -/
theorem noeffect_events (w : World) : stepW w TEv.regWrite = w ∧ stepW w TEv.idle = w ∧ ∀ a, stepW w (TEv.exec a) = w :=
  ⟨rfl, rfl, fun _ => rfl⟩

def Lj : List TEv := [TEv.write 100 1, TEv.exec 100]

theorem Lj_nc : ∀ i, i < Lj.length → ∀ x q e r, preSeq Lj i ≠ TEv.check x q e r :=
  fun i hi x q e r => preSeq_prop Lj (fun ev => ev ≠ TEv.check x q e r) (by simp [Lj]) i hi
theorem Lj_ns : ∀ i, i < Lj.length → ∀ a b, preSeq Lj i ≠ TEv.splitWrite a b :=
  fun i hi a b => preSeq_prop Lj (fun ev => ev ≠ TEv.splitWrite a b) (by simp [Lj]) i hi
theorem Lj_nd : ∀ i, i < Lj.length → ∀ a b, preSeq Lj i ≠ TEv.dmaWrite a b :=
  fun i hi a b => preSeq_prop Lj (fun ev => ev ≠ TEv.dmaWrite a b) (by simp [Lj]) i hi

/-- **Scope witness (injected code).**  Code injected outside the protected range and executed leaves every assumption true and
every alarm silent; it is not an `ExecViolation`.  The scheme, as modelled, does not claim to prevent this. -/
theorem injected_code_outside_goal : ∃ (C : Cost) (sch : Sched (sysP 16).n (honTl Lj)),
    WF (sysP 16) C .L1 .tsc (honTl Lj) ∧ Assumptions (sysP 16) C (honTl Lj) sch ∧
      (∃ j a, honTl Lj j = TEv.exec a ∧ ¬ (sysP 16).prot a ∧ (worldAt (sysP 16) (honTl Lj) j).F a ≠ (sysP 16).I0 a) ∧
      ¬ ExecViolation (sysP 16) (honTl Lj) := by
  have hW : worldAt (sysP 16) (honTl Lj) Lj.length = ⟨wr8 (fun _ => 0) 100 1, wr8 (fun _ => 0) 100 1, false⟩ := by
    simp [honTl, worldAt, stepW, tailTl, preSeq, Lj, World.init, sysP, mkSys]
  obtain ⟨hwf, h1, h2c, h2n, h5, h7, h8, hna⟩ := hon_core 16 (by decide) Lj Lj_nc Lj_ns ⟨fun _ => 2, 1, 1⟩ .L1 .tsc
    (fun i hi => preSeq_prop Lj (fun ev => Level.L1.allows .tsc (honTl Lj) i ev) (by simp [Lj, Level.allows, Level.rank]) i hi)
    _ hW (by intro y hy; simp [wr8]; omega) (by simp [wr8])
  have h3 : A3 (sysP 16) ⟨fun _ => 2, 1, 1⟩ := by intro x hx; simp [sysP, mkSys]
  have hwr : ∀ i, i < Lj.length → ∀ a b, preSeq Lj i = TEv.write a b → a = 100 := by
    intro i hi a b h
    have : preSeq Lj i ∈ Lj := preSeq_mem Lj i hi
    rw [h] at this
    simp only [Lj, List.mem_cons, List.not_mem_nil, or_false, TEv.write.injEq, reduceCtorEq] at this
    exact this.1
  refine ⟨⟨fun _ => 2, 1, 1⟩, honSch 16 Lj Lj_nc, hwf, ⟨h1, mk_cov _ _ _ _ _ _ _ _ _ (by decide), h2c, h2n,
    ⟨0, by decide, tail_intact _ _ _ _ _ _ 0 rfl (fun i hi a b h => by rw [hwr i hi a b h]; simp [sysP, mkSys])⟩, h3,
    tail_a4 _ _ _ _ _ Lj_nd, h5,
    tail_a6 _ _ _ _ _ _ rfl (by decide) Lj_nc (fun i hi a b h hp _ => by rw [hwr i hi a b h] at hp; simp [sysP, mkSys] at hp), h7, h8⟩, ?_, ?_⟩
  · have hw1 : worldAt (sysP 16) (honTl Lj) 1 = ⟨wr8 (fun _ => 0) 100 1, wr8 (fun _ => 0) 100 1, false⟩ := by
      simp [honTl, worldAt, stepW, tailTl, preSeq, Lj, World.init, sysP, mkSys]
    refine ⟨1, 100, by simp [honTl, tailTl, preSeq, Lj], by simp [sysP, mkSys], ?_⟩
    rw [hw1]; simp [wr8, sysP, mkSys]
  · rintro ⟨j, a, hj, hp, _, hF⟩
    obtain ⟨i, b, _, hw, _⟩ := last_write (sysP 16) (honTl Lj) h1 (tail_a4 _ _ _ _ _ Lj_nd) a j hF
    by_cases hi : i < Lj.length
    · rw [show honTl Lj i = preSeq Lj i from tailTl_pre _ _ _ hi] at hw
      have := hwr i hi a b hw
      simp [sysP, mkSys] at hp
      omega
    · simp [honTl, tailTl, hi] at hw

end SmcTamper
