module
public import SmcTamper.Threat.Witnesses
public import SmcTamper.Detection.Reset

@[expose] public section

namespace SmcTamper

/-! ## Witnesses for T3, part 2: honest-check timelines (A2 coverage, A4, A6) -/

/-- The base system with protected range `[0, p)`; `p = 16` is `zSys`. -/
def sysP (p : Nat) : Sys := mkSys (fun _ => 0) 64 16 0x13 8 p 1 1 2

theorem honest_ok_of_region (S : Sys) (x : Nat) (D : Mem) (h : ∀ y, S.inRegion x y → D y = S.I0 y) (hop : D (S.unit x).cu.opAddr = S.I0 (S.unit x).cu.opAddr) :
    checkOk S ⟨D, D, false⟩ x .honest := by
  have hfr : (S.unit x).cu.value ((S.unit x).cu.reset D) = (S.unit x).cu.value ((S.unit x).cu.reset S.I0) := by
    apply value_frame
    intro y hy
    unfold CheckUnit.reset wr8
    by_cases hyo : y = (S.unit x).cu.opAddr
    · simp [hyo]
    · simp only [hyo, ite_false]
      rcases hy with ⟨h1, h2⟩ | h
      · exact h y ⟨h1, by simpa using h2⟩
      · exact absurd h hyo
  simp only [checkOk, Bool.not_false, Sys.expected]
  rw [coherent_viewValue]
  exact hfr

theorem admits_of_nc (C : Cost) (S : Sys) (ev : TEv) (h : ∀ x p e r, ev ≠ TEv.check x p e r) : C.admits S ev := by
  cases ev with
  | check x p e r => exact absurd rfl (h x p e r)
  | _ => simp [Cost.admits]

abbrev honTl (L : List TEv) : Nat → TEv := tailTl (preSeq L) L.length (TEv.check 0 .honest 1 1)

def honSch (p : Nat) (L : List TEv) (hnc : ∀ i, i < L.length → ∀ x q e r, preSeq L i ≠ TEv.check x q e r) :
    Sched (sysP p).n (honTl L) := tailSch (sysP p) rfl (preSeq L) L.length .honest 1 1 hnc

theorem hon_core (p : Nat) (hp : 8 ≤ p) (L : List TEv) (hnc : ∀ i, i < L.length → ∀ x q e r, preSeq L i ≠ TEv.check x q e r)
    (hns : ∀ i, i < L.length → ∀ a b, preSeq L i ≠ TEv.splitWrite a b)
    (C : Cost) (l : Level) (t : TimerSrc) (hpl : ∀ i, i < L.length → l.allows t (honTl L) i (preSeq L i))
    (D0 : Mem) (hW : worldAt (sysP p) (honTl L) L.length = ⟨D0, D0, false⟩) (hreg : ∀ y, y < 16 → D0 y = 0)
    (hop : D0 64 = 0) :
    WF (sysP p) C l t (honTl L) ∧ A1 (sysP p) (honTl L) ∧ A2code (sysP p) ∧ A2conn (sysP p) ∧ A5 (honTl L) ∧ A7 (sysP p) ∧
      A8 (sysP p) (honTl L) (honSch p L hnc) ∧ ¬ Alarm (sysP p) (honTl L) (honSch p L hnc) := by
  have hok : checkOk (sysP p) (worldAt (sysP p) (honTl L) L.length) 0 .honest := by
    rw [hW]
    apply honest_ok_of_region
    · intro y hy
      simp only [Sys.inRegion, sysP, mkSys] at hy
      exact hreg y (by omega)
    · simpa [sysP, mkSys] using hop
  refine ⟨?_, tail_a1 _ _ _ _ _ _ hns, mk_code _ _ _ _ _ _ _ _ _ (by omega), mk_conn _ _ _ _ _ _ _ _ _,
    tail_a5 _ _ _ _ _ rfl hnc, mk_resp _ _ _ _ _ _ _ _ _ (by decide), ?_, ?_⟩
  · refine tail_wf _ _ _ _ _ _ C l t hpl ?_ ?_ ?_ hnc ?_ ?_ ?_
    · intro i; simp [Level.allows]
    · intro i hi; exact admits_of_nc C _ _ (fun x q e r => hnc i hi x q e r)
    · simp [Cost.admits, sysP, mkSys]
    · intro _ a hc _
      rw [hW]
      simp only [sysP, mkSys] at hc ⊢
      exact hreg a (by omega)
    · intro h; cases h
    · intro med h; cases h
  · intro x m e r hx h hex
    exfalso
    obtain ⟨a, hra, _, hne⟩ := hex
    simp only [honSch, tailSch] at hne
    rw [tail_world, hW] at hne
    simp only [sysP, mkSys, Sys.inRegion] at hra hne
    exact hne (hreg a (by omega))
  · exact tail_noalarm (sysP p) _ _ _ _ _ rfl (by simp [sysP, mkSys]) hnc hok (by simp [sysP, mkSys])

/-! ### A4: a physical (DMA) write, use, restore -/

def L4 : List TEv := [TEv.dmaWrite 8 1, TEv.exec 8, TEv.dmaWrite 8 0]

theorem L4_nc : ∀ i, i < L4.length → ∀ x q e r, preSeq L4 i ≠ TEv.check x q e r :=
  fun i hi x q e r => preSeq_prop L4 (fun ev => ev ≠ TEv.check x q e r) (by simp [L4]) i hi
theorem L4_ns : ∀ i, i < L4.length → ∀ a b, preSeq L4 i ≠ TEv.splitWrite a b :=
  fun i hi a b => preSeq_prop L4 (fun ev => ev ≠ TEv.splitWrite a b) (by simp [L4]) i hi
theorem L4_nw : ∀ i, i < L4.length → ∀ a b, preSeq L4 i ≠ TEv.write a b :=
  fun i hi a b => preSeq_prop L4 (fun ev => ev ≠ TEv.write a b) (by simp [L4]) i hi

def D4 : Mem := wr8 (wr8 (fun _ => 0) 8 1) 8 0

theorem nec_A4 : ∃ (C : Cost) (sch : Sched (sysP 16).n (honTl L4)),
    WF (sysP 16) C .L4 .tsc (honTl L4) ∧ AllBut 4 (sysP 16) C (honTl L4) sch ∧ Wins (sysP 16) (honTl L4) sch := by
  have hW : worldAt (sysP 16) (honTl L4) L4.length = ⟨D4, D4, false⟩ := by
    simp [honTl, worldAt, stepW, tailTl, preSeq, L4, World.init, D4, sysP, mkSys]
  obtain ⟨hwf, h1, h2c, h2n, h5, h7, h8, hna⟩ := hon_core 16 (by decide) L4 L4_nc L4_ns ⟨fun _ => 2, 1, 1⟩ .L4 .tsc
    (fun i hi => preSeq_prop L4 (fun ev => Level.L4.allows .tsc (honTl L4) i ev) (by simp [L4, Level.allows, Level.rank]) i hi)
    D4 hW (by intro y hy; simp [D4, wr8]) (by simp [D4, wr8])
  have h3 : A3 (sysP 16) ⟨fun _ => 2, 1, 1⟩ := by intro x hx; simp [sysP, mkSys]
  refine ⟨⟨fun _ => 2, 1, 1⟩, honSch 16 L4 L4_nc, hwf, ⟨Or.inr h1, Or.inr (mk_cov _ _ _ _ _ _ _ _ _ (by decide)), h2c, h2n,
    Or.inr ⟨0, by decide, tail_intact _ _ _ _ _ _ 0 rfl (fun i hi a b h => absurd h (L4_nw i hi a b))⟩, Or.inr h3, Or.inl rfl,
    Or.inr h5, Or.inr (tail_a6 _ _ _ _ _ _ rfl L4_nc (fun i hi a b h => absurd h (L4_nw i hi a b))), h7, Or.inr h8⟩, ?_, hna⟩
  refine tail_exec _ _ _ _ _ _ 1 8 (by simp [L4]) (by simp [preSeq, L4]) (by simp [sysP, mkSys]) (by simp [sysP, mkSys]) ?_
  have : worldAt (sysP 16) (honTl L4) 1 = ⟨wr8 (fun _ => 0) 8 1, wr8 (fun _ => 0) 8 1, false⟩ := by
    simp [honTl, worldAt, stepW, tailTl, preSeq, L4, World.init, sysP, mkSys]
  rw [this]
  simp [wr8, sysP, mkSys]

/-! ### A6: write, execute, restore inside a check gap -/

def L6 : List TEv := [TEv.write 8 1, TEv.exec 8, TEv.write 8 0]

theorem L6_nc : ∀ i, i < L6.length → ∀ x q e r, preSeq L6 i ≠ TEv.check x q e r :=
  fun i hi x q e r => preSeq_prop L6 (fun ev => ev ≠ TEv.check x q e r) (by simp [L6]) i hi
theorem L6_ns : ∀ i, i < L6.length → ∀ a b, preSeq L6 i ≠ TEv.splitWrite a b :=
  fun i hi a b => preSeq_prop L6 (fun ev => ev ≠ TEv.splitWrite a b) (by simp [L6]) i hi
theorem L6_nd : ∀ i, i < L6.length → ∀ a b, preSeq L6 i ≠ TEv.dmaWrite a b :=
  fun i hi a b => preSeq_prop L6 (fun ev => ev ≠ TEv.dmaWrite a b) (by simp [L6]) i hi

theorem nec_A6 : ∃ (C : Cost) (sch : Sched (sysP 16).n (honTl L6)),
    WF (sysP 16) C .L1 .tsc (honTl L6) ∧ AllBut 6 (sysP 16) C (honTl L6) sch ∧ Wins (sysP 16) (honTl L6) sch := by
  have hW : worldAt (sysP 16) (honTl L6) L6.length = ⟨D4, D4, false⟩ := by
    simp [honTl, worldAt, stepW, tailTl, preSeq, L6, World.init, D4, sysP, mkSys]
  obtain ⟨hwf, h1, h2c, h2n, h5, h7, h8, hna⟩ := hon_core 16 (by decide) L6 L6_nc L6_ns ⟨fun _ => 2, 1, 1⟩ .L1 .tsc
    (fun i hi => preSeq_prop L6 (fun ev => Level.L1.allows .tsc (honTl L6) i ev) (by simp [L6, Level.allows, Level.rank]) i hi)
    D4 hW (by intro y hy; simp [D4, wr8]) (by simp [D4, wr8])
  have h3 : A3 (sysP 16) ⟨fun _ => 2, 1, 1⟩ := by intro x hx; simp [sysP, mkSys]
  have hcode : ∀ i, i < L6.length → ∀ a b, preSeq L6 i = TEv.write a b → ¬ ((sysP 16).unit 0).code a := by
    intro i hi a b h
    have : preSeq L6 i ∈ L6 := preSeq_mem L6 i hi
    rw [h] at this
    simp only [L6, List.mem_cons, List.not_mem_nil, or_false, TEv.write.injEq, reduceCtorEq] at this
    have ha8 : a = 8 := by
      rcases this with h | h | h <;> first | omega | exact h.1 | simp_all
    subst ha8
    simp [sysP, mkSys]
  refine ⟨⟨fun _ => 2, 1, 1⟩, honSch 16 L6 L6_nc, hwf, ⟨Or.inr h1, Or.inr (mk_cov _ _ _ _ _ _ _ _ _ (by decide)), h2c, h2n,
    Or.inr ⟨0, by decide, tail_intact _ _ _ _ _ _ 0 rfl hcode⟩, Or.inr h3, Or.inr (tail_a4 _ _ _ _ _ L6_nd),
    Or.inr h5, Or.inl rfl, h7, Or.inr h8⟩, ?_, hna⟩
  refine tail_exec _ _ _ _ _ _ 1 8 (by simp [L6]) (by simp [preSeq, L6]) (by simp [sysP, mkSys]) (by simp [sysP, mkSys]) ?_
  have : worldAt (sysP 16) (honTl L6) 1 = ⟨wr8 (fun _ => 0) 8 1, wr8 (fun _ => 0) 8 1, false⟩ := by
    simp [honTl, worldAt, stepW, tailTl, preSeq, L6, World.init, sysP, mkSys]
  rw [this]
  simp [wr8, sysP, mkSys]

/-! ### A2 (coverage): a protected byte outside every unit's region -/

def Lc : List TEv := [TEv.write 20 1, TEv.exec 20]

theorem Lc_nc : ∀ i, i < Lc.length → ∀ x q e r, preSeq Lc i ≠ TEv.check x q e r :=
  fun i hi x q e r => preSeq_prop Lc (fun ev => ev ≠ TEv.check x q e r) (by simp [Lc]) i hi
theorem Lc_ns : ∀ i, i < Lc.length → ∀ a b, preSeq Lc i ≠ TEv.splitWrite a b :=
  fun i hi a b => preSeq_prop Lc (fun ev => ev ≠ TEv.splitWrite a b) (by simp [Lc]) i hi
theorem Lc_nd : ∀ i, i < Lc.length → ∀ a b, preSeq Lc i ≠ TEv.dmaWrite a b :=
  fun i hi a b => preSeq_prop Lc (fun ev => ev ≠ TEv.dmaWrite a b) (by simp [Lc]) i hi

theorem Lc_write : ∀ i, i < Lc.length → ∀ a b, preSeq Lc i = TEv.write a b → a = 20 ∧ b = 1 := by
  intro i hi a b h
  have : preSeq Lc i ∈ Lc := preSeq_mem Lc i hi
  rw [h] at this
  simp only [Lc, List.mem_cons, List.not_mem_nil, or_false, TEv.write.injEq, reduceCtorEq] at this
  exact this

theorem nec_A2cov : ∃ (C : Cost) (sch : Sched (sysP 21).n (honTl Lc)),
    WF (sysP 21) C .L1 .tsc (honTl Lc) ∧ AllBut 2 (sysP 21) C (honTl Lc) sch ∧ Wins (sysP 21) (honTl Lc) sch := by
  have hW : worldAt (sysP 21) (honTl Lc) Lc.length = ⟨wr8 (fun _ => 0) 20 1, wr8 (fun _ => 0) 20 1, false⟩ := by
    simp [honTl, worldAt, stepW, tailTl, preSeq, Lc, World.init, sysP, mkSys]
  obtain ⟨hwf, h1, h2c, h2n, h5, h7, h8, hna⟩ := hon_core 21 (by decide) Lc Lc_nc Lc_ns ⟨fun _ => 2, 1, 1⟩ .L1 .tsc
    (fun i hi => preSeq_prop Lc (fun ev => Level.L1.allows .tsc (honTl Lc) i ev) (by simp [Lc, Level.allows, Level.rank]) i hi)
    _ hW (by intro y hy; simp [wr8]; omega) (by simp [wr8])
  have h3 : A3 (sysP 21) ⟨fun _ => 2, 1, 1⟩ := by intro x hx; simp [sysP, mkSys]
  have hcode : ∀ i, i < Lc.length → ∀ a b, preSeq Lc i = TEv.write a b → ¬ ((sysP 21).unit 0).code a := by
    intro i hi a b h
    obtain ⟨rfl, _⟩ := Lc_write i hi a b h
    simp [sysP, mkSys]
  refine ⟨⟨fun _ => 2, 1, 1⟩, honSch 21 Lc Lc_nc, hwf, ⟨Or.inr h1, Or.inl rfl, h2c, h2n,
    Or.inr ⟨0, by decide, tail_intact _ _ _ _ _ _ 0 rfl hcode⟩, Or.inr h3, Or.inr (tail_a4 _ _ _ _ _ Lc_nd),
    Or.inr h5, Or.inr (tail_a6 _ _ _ _ _ _ rfl Lc_nc ?_), h7, Or.inr h8⟩, ?_, hna⟩
  · intro i hi a b h _ _
    obtain ⟨rfl, rfl⟩ := Lc_write i hi a b h
    rw [hW]
    simp [wr8, sysP, mkSys]
  · refine tail_exec _ _ _ _ _ _ 1 20 (by simp [Lc]) (by simp [preSeq, Lc]) (by simp [sysP, mkSys]) (by simp [sysP, mkSys]) ?_
    have : worldAt (sysP 21) (honTl Lc) 1 = ⟨wr8 (fun _ => 0) 20 1, wr8 (fun _ => 0) 20 1, false⟩ := by
      simp [honTl, worldAt, stepW, tailTl, preSeq, Lc, World.init, sysP, mkSys]
    rw [this]
    simp [wr8, sysP, mkSys]

end SmcTamper
