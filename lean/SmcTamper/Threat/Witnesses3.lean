module
public import SmcTamper.Threat.Witnesses2
public import SmcTamper.Detection.Predicate

@[expose] public section

namespace SmcTamper

/-! ## Witnesses for T3, part 3: neutralisation (A2), split views (A1), compensation (A8) -/

/-! ### A2 (one intact unit): neutralise the only unit, then run it as a no-op -/

def Ln : List TEv := [TEv.write 3 1, TEv.exec 3]

theorem Ln_nc : ∀ i, i < Ln.length → ∀ x q e r, preSeq Ln i ≠ TEv.check x q e r :=
  fun i hi x q e r => preSeq_prop Ln (fun ev => ev ≠ TEv.check x q e r) (by simp [Ln]) i hi
theorem Ln_ns : ∀ i, i < Ln.length → ∀ a b, preSeq Ln i ≠ TEv.splitWrite a b :=
  fun i hi a b => preSeq_prop Ln (fun ev => ev ≠ TEv.splitWrite a b) (by simp [Ln]) i hi
theorem Ln_nd : ∀ i, i < Ln.length → ∀ a b, preSeq Ln i ≠ TEv.dmaWrite a b :=
  fun i hi a b => preSeq_prop Ln (fun ev => ev ≠ TEv.dmaWrite a b) (by simp [Ln]) i hi
theorem Ln_write : ∀ i, i < Ln.length → ∀ a b, preSeq Ln i = TEv.write a b → a = 3 ∧ b = 1 := by
  intro i hi a b h
  have : preSeq Ln i ∈ Ln := preSeq_mem Ln i hi
  rw [h] at this
  simp only [Ln, List.mem_cons, List.not_mem_nil, or_false, TEv.write.injEq, reduceCtorEq] at this
  exact this

abbrev nTl : Nat → TEv := tailTl (preSeq Ln) Ln.length (TEv.check 0 .neutral 1 1)

def nSch : Sched (sysP 16).n nTl := tailSch (sysP 16) rfl (preSeq Ln) Ln.length .neutral 1 1 Ln_nc

theorem nec_A2intact : ∃ (C : Cost) (sch : Sched (sysP 16).n nTl),
    WF (sysP 16) C .L1 .tsc nTl ∧ AllBut 12 (sysP 16) C nTl sch ∧ Wins (sysP 16) nTl sch := by
  have hW : worldAt (sysP 16) nTl Ln.length = ⟨wr8 (fun _ => 0) 3 1, wr8 (fun _ => 0) 3 1, false⟩ := by
    simp [nTl, worldAt, stepW, tailTl, preSeq, Ln, World.init, sysP, mkSys]
  have h3 : A3 (sysP 16) ⟨fun _ => 2, 1, 1⟩ := by intro x hx; simp [sysP, mkSys]
  refine ⟨⟨fun _ => 2, 1, 1⟩, nSch, ?_, ⟨Or.inr (tail_a1 _ _ _ _ _ _ Ln_ns), Or.inr (mk_cov _ _ _ _ _ _ _ _ _ (by decide)),
    mk_code _ _ _ _ _ _ _ _ _ (by decide), mk_conn _ _ _ _ _ _ _ _ _, Or.inl rfl, Or.inr h3, Or.inr (tail_a4 _ _ _ _ _ Ln_nd),
    Or.inr (tail_a5 _ _ _ _ _ rfl Ln_nc), Or.inr (tail_a6 _ _ _ _ _ _ rfl Ln_nc ?_),
    mk_resp _ _ _ _ _ _ _ _ _ (by decide), Or.inr ?_⟩, ?_⟩
  · refine tail_wf _ _ _ _ _ _ _ .L1 .tsc ?_ ?_ ?_ ?_ Ln_nc (by simp) ?_ (by simp)
    · intro i hi
      exact preSeq_prop Ln (fun ev => Level.L1.allows .tsc nTl i ev) (by simp [Ln, Level.allows, Level.rank]) i hi
    · intro i; simp [Level.allows, Level.rank]
    · intro i hi; exact admits_of_nc _ _ _ (fun x q e r => Ln_nc i hi x q e r)
    · simp [Cost.admits]
    · intro _
      refine ⟨3, by simp [sysP, mkSys], by simp [sysP, mkSys], ?_⟩
      rw [hW]; simp [wr8, sysP, mkSys]
  · intro i hi a b h _ _
    obtain ⟨rfl, rfl⟩ := Ln_write i hi a b h
    rw [hW]; simp [wr8, sysP, mkSys]
  · intro x m e r _ h
    simp only [nSch, tailSch, nTl] at h
    rw [tailTl_tail] at h
    simp at h
  · refine ⟨tail_exec _ _ _ _ _ _ 1 3 (by simp [Ln]) (by simp [preSeq, Ln]) (by simp [sysP, mkSys]) (by simp [sysP, mkSys]) ?_,
      tail_noalarm (sysP 16) _ _ _ _ _ rfl (by simp [sysP, mkSys]) Ln_nc (by simp [checkOk]) (by simp [sysP, mkSys])⟩
    have : worldAt (sysP 16) nTl 1 = ⟨wr8 (fun _ => 0) 3 1, wr8 (fun _ => 0) 3 1, false⟩ := by
      simp [nTl, worldAt, stepW, tailTl, preSeq, Ln, World.init, sysP, mkSys]
    rw [this]; simp [wr8, sysP, mkSys]

/-! ### A1: a split-memory attack on a unit whose kernel is a plain checksum (all toggles zero) -/

def I1 : Mem := fun a => if a = 0 then 1 else if a = 64 then 0x13 else 0

def sys1 : Sys := mkSys I1 64 8 0x13 4 8 1 1 2

def Ls : List TEv := [TEv.splitWrite 5 1, TEv.exec 5]

theorem Ls_nc : ∀ i, i < Ls.length → ∀ x q e r, preSeq Ls i ≠ TEv.check x q e r :=
  fun i hi x q e r => preSeq_prop Ls (fun ev => ev ≠ TEv.check x q e r) (by simp [Ls]) i hi
theorem Ls_nd : ∀ i, i < Ls.length → ∀ a b, preSeq Ls i ≠ TEv.dmaWrite a b :=
  fun i hi a b => preSeq_prop Ls (fun ev => ev ≠ TEv.dmaWrite a b) (by simp [Ls]) i hi
theorem Ls_nw : ∀ i, i < Ls.length → ∀ a b, preSeq Ls i ≠ TEv.write a b :=
  fun i hi a b => preSeq_prop Ls (fun ev => ev ≠ TEv.write a b) (by simp [Ls]) i hi

abbrev sTl : Nat → TEv := tailTl (preSeq Ls) Ls.length (TEv.check 0 .honest 1 1)

def sSch : Sched sys1.n sTl := tailSch sys1 rfl (preSeq Ls) Ls.length .honest 1 1 Ls_nc

theorem nec_A1 : ∃ (C : Cost) (sch : Sched sys1.n sTl),
    WF sys1 C .L2 .tsc sTl ∧ AllBut 1 sys1 C sTl sch ∧ Wins sys1 sTl sch := by
  have hW : worldAt sys1 sTl Ls.length = ⟨wr8 I1 5 1, I1, true⟩ := by
    simp [sTl, worldAt, stepW, tailTl, preSeq, Ls, World.init, sys1, mkSys]
  have h3 : A3 sys1 ⟨fun _ => 2, 1, 1⟩ := by intro x hx; simp [sys1, mkSys]
  have hok : checkOk sys1 (worldAt sys1 sTl Ls.length) 0 .honest := by
    rw [hW]
    simp only [checkOk, Bool.not_true, Sys.expected]
    decide +kernel
  refine ⟨⟨fun _ => 2, 1, 1⟩, sSch, ?_, ⟨Or.inl rfl, Or.inr (mk_cov _ _ _ _ _ _ _ _ _ (by decide)),
    mk_code _ _ _ _ _ _ _ _ _ (by decide), mk_conn _ _ _ _ _ _ _ _ _,
    Or.inr ⟨0, by decide, tail_intact _ _ _ _ _ _ 0 rfl (fun i hi a b h => absurd h (Ls_nw i hi a b))⟩, Or.inr h3,
    Or.inr (tail_a4 _ _ _ _ _ Ls_nd), Or.inr (tail_a5 _ _ _ _ _ rfl Ls_nc),
    Or.inr (tail_a6 _ _ _ _ _ _ rfl Ls_nc (fun i hi a b h => absurd h (Ls_nw i hi a b))),
    mk_resp _ _ _ _ _ _ _ _ _ (by decide), Or.inr ?_⟩, ?_⟩
  · refine tail_wf _ _ _ _ _ _ _ .L2 .tsc ?_ ?_ ?_ ?_ Ls_nc ?_ (by simp) (by simp)
    · intro i hi
      exact preSeq_prop Ls (fun ev => Level.L2.allows .tsc sTl i ev) (by simp [Ls, Level.allows, Level.rank]) i hi
    · intro i; simp [Level.allows]
    · intro i hi; exact admits_of_nc _ _ _ (fun x q e r => Ls_nc i hi x q e r)
    · simp [Cost.admits, sys1, mkSys]
    · intro _ a hc _
      rw [hW]
      simp only [sys1, mkSys] at hc ⊢
      simp [wr8]
      omega
  · intro x m e r _ h hex
    exfalso
    obtain ⟨a, _, _, hne⟩ := hex
    simp only [sSch, tailSch, sTl] at hne
    rw [tail_world, hW] at hne
    exact hne rfl
  · refine ⟨tail_exec _ _ _ _ _ _ 1 5 (by simp [Ls]) (by simp [preSeq, Ls]) (by simp [sys1, mkSys]) (by simp [sys1, mkSys]) ?_,
      tail_noalarm sys1 _ _ _ _ _ rfl (by simp [sys1, mkSys]) Ls_nc hok (by simp [sys1, mkSys])⟩
    have : worldAt sys1 sTl 1 = ⟨wr8 I1 5 1, I1, true⟩ := by
      simp [sTl, worldAt, stepW, tailTl, preSeq, Ls, World.init, sys1, mkSys]
    rw [this]; simp [wr8, sys1, mkSys, I1]

/-! ### A8: compensation.  Two qwords are changed so that the kernel's (sum, opcode state) is unchanged (the P04 pair). -/

def sys8 : Sys := mkSys (collMem 0) 64 16 0x13 8 16 1 1 2

def L8 : List TEv := [TEv.write 8 1, TEv.write 15 0x80, TEv.exec 8]

theorem L8_nc : ∀ i, i < L8.length → ∀ x q e r, preSeq L8 i ≠ TEv.check x q e r :=
  fun i hi x q e r => preSeq_prop L8 (fun ev => ev ≠ TEv.check x q e r) (by simp [L8]) i hi
theorem L8_ns : ∀ i, i < L8.length → ∀ a b, preSeq L8 i ≠ TEv.splitWrite a b :=
  fun i hi a b => preSeq_prop L8 (fun ev => ev ≠ TEv.splitWrite a b) (by simp [L8]) i hi
theorem L8_nd : ∀ i, i < L8.length → ∀ a b, preSeq L8 i ≠ TEv.dmaWrite a b :=
  fun i hi a b => preSeq_prop L8 (fun ev => ev ≠ TEv.dmaWrite a b) (by simp [L8]) i hi
theorem L8_write : ∀ i, i < L8.length → ∀ a b, preSeq L8 i = TEv.write a b → (a = 8 ∧ b = 1) ∨ (a = 15 ∧ b = 0x80) := by
  intro i hi a b h
  have : preSeq L8 i ∈ L8 := preSeq_mem L8 i hi
  rw [h] at this
  simp only [L8, List.mem_cons, List.not_mem_nil, or_false, TEv.write.injEq, reduceCtorEq] at this
  rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; subst h1; subst h2; exact ⟨rfl, rfl⟩
  · right; subst h1; subst h2; exact ⟨rfl, rfl⟩

abbrev cTl : Nat → TEv := tailTl (preSeq L8) L8.length (TEv.check 0 .honest 1 1)

def cSch : Sched sys8.n cTl := tailSch sys8 rfl (preSeq L8) L8.length .honest 1 1 L8_nc

def D8 : Mem := wr8 (wr8 (collMem 0) 8 1) 15 0x80

theorem D8_value : collUnit.value (collUnit.reset D8) = collUnit.value (collUnit.reset (collMem 0)) := by
  decide +kernel

theorem nec_A8 : ∃ (C : Cost) (sch : Sched sys8.n cTl),
    WF sys8 C .L1 .tsc cTl ∧ AllBut 8 sys8 C cTl sch ∧ Wins sys8 cTl sch := by
  have hW : worldAt sys8 cTl L8.length = ⟨D8, D8, false⟩ := by
    simp [cTl, worldAt, stepW, tailTl, preSeq, L8, World.init, D8, sys8, mkSys]
  have h3 : A3 sys8 ⟨fun _ => 2, 1, 1⟩ := by intro x hx; simp [sys8, mkSys]
  have hok : checkOk sys8 (worldAt sys8 cTl L8.length) 0 .honest := by
    rw [hW]
    simp only [checkOk, Bool.not_false, Sys.expected]
    rw [coherent_viewValue]
    exact D8_value
  have hcode : ∀ i, i < L8.length → ∀ a b, preSeq L8 i = TEv.write a b → ¬ (sys8.unit 0).code a := by
    intro i hi a b h
    rcases L8_write i hi a b h with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp [sys8, mkSys]
  refine ⟨⟨fun _ => 2, 1, 1⟩, cSch, ?_, ⟨Or.inr (tail_a1 _ _ _ _ _ _ L8_ns), Or.inr (mk_cov _ _ _ _ _ _ _ _ _ (by decide)),
    mk_code _ _ _ _ _ _ _ _ _ (by decide), mk_conn _ _ _ _ _ _ _ _ _,
    Or.inr ⟨0, by decide, tail_intact _ _ _ _ _ _ 0 rfl hcode⟩, Or.inr h3,
    Or.inr (tail_a4 _ _ _ _ _ L8_nd), Or.inr (tail_a5 _ _ _ _ _ rfl L8_nc),
    Or.inr (tail_a6 _ _ _ _ _ _ rfl L8_nc ?_),
    mk_resp _ _ _ _ _ _ _ _ _ (by decide), Or.inl rfl⟩, ?_⟩
  · refine tail_wf _ _ _ _ _ _ _ .L1 .tsc ?_ ?_ ?_ ?_ L8_nc ?_ (by simp) (by simp)
    · intro i hi
      exact preSeq_prop L8 (fun ev => Level.L1.allows .tsc cTl i ev) (by simp [L8, Level.allows, Level.rank]) i hi
    · intro i; simp [Level.allows]
    · intro i hi; exact admits_of_nc _ _ _ (fun x q e r => L8_nc i hi x q e r)
    · simp [Cost.admits, sys8, mkSys]
    · intro _ a hc _
      rw [hW]
      simp only [sys8, mkSys] at hc ⊢
      have h8 : a ≠ 8 := by omega
      have h15 : a ≠ 15 := by omega
      simp [D8, wr8, h8, h15]
  · intro i hi a b h _ _
    rw [hW]
    rcases L8_write i hi a b h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [D8, wr8, sys8, mkSys, collMem]
  · refine ⟨tail_exec _ _ _ _ _ _ 2 8 (by simp [L8]) (by simp [preSeq, L8]) (by simp [sys8, mkSys]) (by simp [sys8, mkSys]) ?_,
      tail_noalarm sys8 _ _ _ _ _ rfl (by simp [sys8, mkSys]) L8_nc hok (by simp [sys8, mkSys])⟩
    have : worldAt sys8 cTl 2 = ⟨wr8 (wr8 (collMem 0) 8 1) 15 0x80, wr8 (wr8 (collMem 0) 8 1) 15 0x80, false⟩ := by
      simp [cTl, worldAt, stepW, tailTl, preSeq, L8, World.init, sys8, mkSys]
    rw [this]; simp [wr8, sys8, mkSys, collMem]

end SmcTamper
