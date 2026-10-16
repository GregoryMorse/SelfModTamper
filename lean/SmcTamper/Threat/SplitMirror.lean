module
public import SmcTamper.Threat.T3

@[expose] public section

namespace SmcTamper

/-! ## T2: split views against the SMC kernel (what mirroring costs)

With separate fetch and data views the kernel fetches its opcode byte from `F` and writes the toggled byte into `D`.  A run is
*faithful* when the fetched opcode equals the data-view opcode at every iteration, i.e. the run is the Level-1 trajectory.  After an
iteration with a non-zero toggle the data-view opcode changes, so a faithful run needs the adversary to copy it into `F`: one
`mediate` event per such iteration.  Each mediation costs at least `km` (cost contract), so with A3 and A5 a faithful mediated
check is a timing failure.  Without mediation the run is not faithful (it executes the stale opcode); whether its value differs is
then the question A8 answers for that run, and for a plain checksum (no opcode state) split views are invisible (`nec_A1`). -/

/-- The toggle of the next iteration from the state `s`. -/
def toggleAt (opAddr : Nat) (s : VState) : Nat := toggle (kAlu (s.F opAddr) s.sum (rd64 s.D s.ptr)).1

/-- The fetched opcode equals the data-view opcode at the start of each of the `n` iterations. -/
def Faithful (opAddr : Nat) (med : Nat → Bool) : Nat → Nat → VState → Prop
  | _, 0, _ => True
  | i, n + 1, s => s.F opAddr = s.D opAddr ∧ Faithful opAddr med (i + 1) n (vStep opAddr (med i) s)

theorem toggle_lt (r : BitVec 64) : toggle r < 6 := by
  unfold toggle
  cases pf r <;> cases sf r <;> simp

theorem xor_toggle_ne (b : BitVec 8) (t : Nat) (h0 : t ≠ 0) (h1 : t < 6) : b ^^^ (BitVec.ofNat 8 t <<< 3) ≠ b := by
  revert b
  have : t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl <;> decide

/-- **T2 (mirroring is forced).**  In a faithful run, every iteration with a non-zero toggle that is followed by another fetch is
mediated. -/
theorem faithful_needs_med (opAddr : Nat) (med : Nat → Bool) :
    ∀ (n i : Nat) (s : VState), Faithful opAddr med i n s → ∀ j, j + 1 < n →
      toggleAt opAddr (vRun opAddr med i j s) ≠ 0 → med (i + j) = true := by
  intro n
  induction n with
  | zero => intro i s _ j hj; omega
  | succ n ih =>
    intro i s hf j hj ht
    obtain ⟨hFD, hf'⟩ := hf
    cases j with
    | zero =>
      simp only [vRun, toggleAt] at ht
      refine Classical.byContradiction (fun hm => ?_)
      have hm' : med i = false := by simpa using hm
      cases n with
      | zero => omega
      | succ n =>
        obtain ⟨hFD', _⟩ := hf'
        simp only [vStep, hm', ite_false, wr8, ite_true] at hFD'
        exact xor_toggle_ne (s.D opAddr) _ ht (toggle_lt _) (hFD'.symm.trans hFD)
    | succ j =>
      have := ih (i + 1) _ hf' j (by omega) (by simpa [vRun] using ht)
      simpa [Nat.add_assoc, Nat.add_comm 1 j] using this

/-- A run that is faithful and in which some non-final iteration toggles needs at least one mediation among its iterations. -/
theorem faithful_med_count (cu : CheckUnit) (med : Nat → Bool) (s0 : VState) (hf : Faithful cu.opAddr med 0 (cu.size / 8) s0)
    (j : Nat) (hj : j + 1 < cu.size / 8) (ht : toggleAt cu.opAddr (vRun cu.opAddr med 0 j s0) ≠ 0) :
    1 ≤ (List.range (cu.size / 8)).countP med := by
  have := faithful_needs_med cu.opAddr med (cu.size / 8) 0 s0 hf j hj ht
  rw [Nat.zero_add] at this
  have hmem : j ∈ List.range (cu.size / 8) := List.mem_range.mpr (by omega)
  exact List.countP_pos_iff.mpr ⟨j, hmem, by simpa using this⟩

/-- **T2 (cost).**  Under A3 and A5, a faithful mediated check of a unit whose opcode state changes before the last iteration is a
timing failure. -/
theorem mediated_timefail (S : Sys) (C : Cost) (tl : Nat → TEv) (hA3 : A3 S C) (hA5 : A5 tl) (c x : Nat) (med : Nat → Bool)
    (e r : Nat) (hx : x < S.n) (hev : tl c = TEv.check x (.mediated med) e r) (hadm : C.admits S (tl c))
    (s0 : VState) (hf : Faithful (S.unit x).cu.opAddr med 0 ((S.unit x).cu.size / 8) s0)
    (j : Nat) (hj : j + 1 < (S.unit x).cu.size / 8)
    (ht : toggleAt (S.unit x).cu.opAddr (vRun (S.unit x).cu.opAddr med 0 j s0) ≠ 0) : timeFailAt S tl c x := by
  have hcnt := faithful_med_count (S.unit x).cu med s0 hf j hj ht
  rw [hev] at hadm
  simp only [Cost.admits] at hadm
  have hr := hA5 c x _ e r hev
  obtain ⟨_, _, _, h4⟩ := hA3 x hx
  refine ⟨_, e, r, hev, ?_⟩
  have : C.km * 1 ≤ C.km * ((List.range ((S.unit x).cu.size / 8)).countP med) := Nat.mul_le_mul_left _ hcnt
  omega

/-- The premise is satisfiable: on the all-zero image with opcode `ADC` the first iteration toggles (even parity), and the unit
has more than one iteration. -/
theorem smc_active_example :
    toggleAt 64 ⟨wr8 (fun _ => 0) 64 0x13, wr8 (fun _ => 0) 64 0x13, 0, 0⟩ ≠ 0 := by
  decide +kernel

end SmcTamper
