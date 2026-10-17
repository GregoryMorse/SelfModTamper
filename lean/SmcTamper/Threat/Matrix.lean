module
public import SmcTamper.Threat.SplitMirror
public import SmcTamper.Contract.Timers

@[expose] public section

namespace SmcTamper

/-! ## T4: the level matrix

* L0 and L1 with the inline timer: the level conditions give A1, A4 and A5 (`tsc_low_level`).
* L1 with an operating-system timer API: readings can be forged (user-mode hooking), so A5 fails (`nec_A5_osApi`).
* L2 (view separation, RDTSC trapping or offsetting): A1 and A5 fail (`nec_A1`, `nec_A5`).
* L4 (physical writers): A4 fails (`nec_A4`).

The capabilities of L2 and above are contract fields in `Level.forgesReading` / `Level.allows`; their sources (Intel SDM for
`CR4.TSD`, VMX RDTSC exiting, TSC offsetting, EPT; Microsoft Learn for `WriteProcessMemory`, `SetThreadContext`) are recorded in
`lean/THREAT_MODEL.md`, not proved here.  With a time source outside the adversary's control (resolution `r`, jitter `j`) the
slowdowns of at least `j + 2r` are still detected (`ext_clock_detects`); smaller ones can be invisible (`reading_indistinguishable`). -/

/-- **T4, L1 with an OS timer.**  The same replay witness as `nec_A5`, with a user-mode adversary and the OS timer API. -/
theorem nec_A5_osApi : ∃ (C : Cost) (sch : Sched zSys.n (zTlE 100 1)),
    WF zSys C .L1 .osApi (zTlE 100 1) ∧ AllBut 5 zSys C (zTlE 100 1) sch ∧ Wins zSys (zTlE 100 1) sch ∧ ¬ A5 (zTlE 100 1) := by
  obtain ⟨hwf, h1, h2, h2c, h2n, h12, h4, h6, h7, h8, hw⟩ :=
    zE_core ⟨fun _ => 2, 1, 1⟩ .L1 .osApi 100 1 (by decide) (Or.inr (by simp [Level.forgesReading, Level.rank])) (by decide) (by decide)
  have h3 : A3 zSys ⟨fun _ => 2, 1, 1⟩ := by intro x hx; simp [zSys, mkSys]
  refine ⟨⟨fun _ => 2, 1, 1⟩, zSchE 100 1, hwf, ?_, hw, ?_⟩
  · exact ⟨Or.inr h1, Or.inr h2, h2c, h2n, Or.inr h12, Or.inr h3, Or.inr h4, Or.inl rfl, Or.inr h6, h7, Or.inr h8⟩
  · intro h
    have := h (zL.length) 0 .emulated 100 1 (by simp [zTlE, tailTl])
    omega

/-- **T4 (matrix).**  What each level gives and loses. -/
theorem T4 :
    -- levels below L2 with the inline timer: A1, A4, A5 follow
    (∀ (S : Sys) (C : Cost) (l : Level) (tl : Nat → TEv), WF S C l .tsc tl → l.rank < 2 →
      (∀ n, (worldAt S tl n).split = false) ∧ (∀ i a b, tl i ≠ TEv.dmaWrite a b) ∧
        (∀ i x p e r, tl i = TEv.check x p e r → r = e)) ∧
    -- L1 with the OS timer API: A5 can fail with a winning adversary
    (∃ (C : Cost) (sch : Sched zSys.n (zTlE 100 1)), WF zSys C .L1 .osApi (zTlE 100 1) ∧ AllBut 5 zSys C (zTlE 100 1) sch ∧
      Wins zSys (zTlE 100 1) sch ∧ ¬ A5 (zTlE 100 1)) ∧
    -- L2: A5 (replayed readings) and A1 (split views) can fail with a winning adversary
    (∃ (C : Cost) (sch : Sched zSys.n (zTlE 100 1)), WF zSys C .L2 .tsc (zTlE 100 1) ∧ AllBut 5 zSys C (zTlE 100 1) sch ∧
      Wins zSys (zTlE 100 1) sch ∧ ¬ A5 (zTlE 100 1)) ∧
    (∃ (C : Cost) (sch : Sched sys1.n sTl), WF sys1 C .L2 .tsc sTl ∧ AllBut 1 sys1 C sTl sch ∧ Wins sys1 sTl sch ∧ ¬ A1 sys1 sTl) ∧
    -- L4: A4 (physical writes) can fail with a winning adversary
    (∃ (C : Cost) (sch : Sched (sysP 16).n (honTl L4)), WF (sysP 16) C .L4 .tsc (honTl L4) ∧ AllBut 4 (sysP 16) C (honTl L4) sch ∧
      Wins (sysP 16) (honTl L4) sch ∧ ¬ A4 (honTl L4)) := by
  refine ⟨fun S C l tl hwf h => tsc_low_level S C l tl hwf h, ?_, ?_, ?_, ?_⟩
  · obtain ⟨C, sch, h1, h2, h3, h4⟩ := nec_A5_osApi; exact ⟨C, sch, h1, h2, h3, h4⟩
  · obtain ⟨C, sch, h1, h2, h3, h4⟩ := nec_A5; exact ⟨C, sch, h1, h2, h3, h4⟩
  · obtain ⟨C, sch, h1, h2, h3⟩ := nec_A1
    exact ⟨C, sch, h1, h2, h3, not_holds sys1 C .L2 .tsc sTl sch h1 h3 1 (by omega) h2⟩
  · obtain ⟨C, sch, h1, h2, h3⟩ := nec_A4
    exact ⟨C, sch, h1, h2, h3, not_holds (sysP 16) C .L4 .tsc (honTl L4) sch h1 h3 4 (by omega) h2⟩

/-! ### An external clock: resolution plus jitter -/

/-- A reading of a run of true duration `d` with an external timer of resolution `r > 0`, where native runs last at most
`native + j` (jitter `j`): the calibrated threshold `(native + j)/r + 1` accepts every native run ... -/
theorem ext_clock_calibrated (r φ s native j d0 : Nat) (hr : 0 < r) (hd : d0 ≤ native + j) :
    reading r φ s (s + d0) ≤ (native + j) / r + 1 := by
  have := (reading_bounds r φ s d0 hr).2
  have := Nat.div_le_div_right (c := r) hd
  omega

/-- ... and rejects every run slowed by `j + 2r` or more. -/
theorem ext_clock_detects (r φ s native j d : Nat) (hr : 0 < r) (hd : native + j + 2 * r ≤ d) :
    (native + j) / r + 1 < reading r φ s (s + d) := by
  have h1 := (reading_bounds r φ s d hr).1
  have h2 : (native + j + 2 * r) / r = (native + j) / r + 2 := by
    rw [show native + j + 2 * r = (native + j) + r * 2 by omega, Nat.add_mul_div_left _ _ hr]
  have h3 := Nat.div_le_div_right (c := r) hd
  omega

end SmcTamper
