module
public import SmcTamper.Threat.Loop

@[expose] public section

namespace SmcTamper

/-! ## Witnesses for T3, part 5: two units (A2 connectivity, A2 code protected) -/

abbrev Zm : Mem := fun _ => 0

theorem step_check (w : World) (x : Nat) (p : CheckPath) (e r : Nat) : stepW w (TEv.check x p e r) = w := rfl
theorem step_idle (w : World) : stepW w TEv.idle = w := rfl
theorem step_exec (w : World) (a : Nat) : stepW w (TEv.exec a) = w := rfl

theorem preSeq_two (a b : TEv) (i : Nat) (hi : i < 2) : preSeq [a, b] i = if i = 0 then a else b := by
  have : i = 0 ∨ i = 1 := by omega
  rcases this with rfl | rfl <;> rfl

/-! ### A2 connectivity: unit 1's code is not covered by unit 0 -/

def qSys : Sys := duoSys (fun a => a < 32) 16 16 16
def qPre : Nat → TEv := preSeq [TEv.write 16 1, TEv.exec 16]
def qB0 : TEv := TEv.check 0 .honest 1 1
def qB1 : TEv := TEv.check 1 .neutral 1 1
abbrev qTl : Nat → TEv := loopTl qPre 2 qB0 qB1 TEv.idle TEv.idle
def qPos : Nat → Nat := fun x => if x = 0 then 0 else 1

theorem qPre_nc : ∀ i, i < 2 → ∀ x p e r, qPre i ≠ TEv.check x p e r := by
  intro i hi x p e r
  have : i = 0 ∨ i = 1 := by omega
  rcases this with rfl | rfl <;> simp [qPre, preSeq]

def qSch : Sched qSys.n qTl :=
  loopSch qPre 2 qB0 qB1 TEv.idle TEv.idle qSys rfl qPos
    (by intro x hx; by_cases h : x = 0 <;> simp [qPos, h])
    (by intro x hx; by_cases h : x = 0
        · subst h; exact ⟨.honest, 1, 1, by simp [qPos, bAt, qB0]⟩
        · have : x = 1 := by omega
          subst this; exact ⟨.neutral, 1, 1, by simp [qPos, bAt, qB1]⟩)
    (by intro j hj x p e r h hx
        have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
        rcases this with rfl | rfl | rfl | rfl <;> simp [bAt, qB0, qB1, qPos] at h ⊢ <;>
          first | omega | (obtain ⟨rfl, _⟩ := h; simp) | (obtain ⟨rfl, _⟩ := h; simp [qPos]) )
    qPre_nc

theorem qW0 : worldAt qSys qTl 2 = ⟨wr8 Zm 16 1, wr8 Zm 16 1, false⟩ := by
  simp [worldAt, stepW, qTl, loopTl, qPre, preSeq, World.init, qSys, duoSys]
  rfl

theorem qW : ∀ i, 2 ≤ i → worldAt qSys qTl i = ⟨wr8 Zm 16 1, wr8 Zm 16 1, false⟩ := by
  have hper : stepW (stepW (stepW (stepW (worldAt qSys qTl 2) qB0) qB1) TEv.idle) TEv.idle = worldAt qSys qTl 2 := by
    simp [step_check, step_idle, qB0, qB1]
  intro i hi
  rw [loop_world_mod qPre 2 qB0 qB1 TEv.idle TEv.idle qSys hper i hi, qW0]
  have : (i - 2) % 4 = 0 ∨ (i - 2) % 4 = 1 ∨ (i - 2) % 4 = 2 ∨ (i - 2) % 4 = 3 := by omega
  rcases this with h | h | h | h <;> rw [h] <;> simp [loopW, step_check, step_idle, qB0, qB1]

theorem qW1 : worldAt qSys qTl 1 = ⟨wr8 Zm 16 1, wr8 Zm 16 1, false⟩ := by
  simp [worldAt, stepW, qTl, loopTl, qPre, preSeq, World.init, qSys, duoSys]
  rfl

theorem q_no_conn : ¬ A2conn qSys := by
  intro h
  have hr := h 0 1 (by decide) (by decide)
  have key : ∀ z, Reach qSys 0 z → z = 0 := by
    intro z hz
    induction hz with
    | refl _ => rfl
    | @step y z' hy hz'n hcov ih =>
      subst ih
      refine Classical.byContradiction (fun hne => ?_)
      have hz1 : z' = 1 := by have : z' < 2 := hz'n; omega
      subst hz1
      have := hcov 16 (by simp [qSys, duoSys]) (by simp [qSys, duoSys])
      simp [qSys, duoSys, Sys.inRegion] at this
  have := key 1 hr
  omega


theorem qchk : ∀ i x p e r, qTl i = TEv.check x p e r → 2 ≤ i ∧
    (((i - 2) % 4 = 0 ∧ x = 0 ∧ p = .honest ∧ e = 1 ∧ r = 1) ∨ ((i - 2) % 4 = 1 ∧ x = 1 ∧ p = .neutral ∧ e = 1 ∧ r = 1)) := by
  intro i x p e r h
  by_cases hi : i < 2
  · unfold qTl at h
    rw [loopTl_pre qPre 2 qB0 qB1 TEv.idle TEv.idle hi] at h
    exact absurd h (qPre_nc i hi x p e r)
  · have hi' : 2 ≤ i := by omega
    refine ⟨hi', ?_⟩
    unfold qTl at h
    rw [loopTl_body qPre 2 qB0 qB1 TEv.idle TEv.idle hi'] at h
    have : (i - 2) % 4 = 0 ∨ (i - 2) % 4 = 1 ∨ (i - 2) % 4 = 2 ∨ (i - 2) % 4 = 3 := by omega
    rcases this with h0 | h0 | h0 | h0 <;> rw [h0] at h <;> simp [bAt, qB0, qB1] at h
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := h; exact Or.inl ⟨h0, rfl, rfl, rfl, rfl⟩
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := h; exact Or.inr ⟨h0, rfl, rfl, rfl, rfl⟩

theorem qwrite : ∀ i a b, qTl i = TEv.write a b → a = 16 ∧ b = 1 := by
  intro i a b h
  by_cases hi : i < 2
  · unfold qTl at h
    rw [loopTl_pre qPre 2 qB0 qB1 TEv.idle TEv.idle hi] at h
    have : i = 0 ∨ i = 1 := by omega
    rcases this with rfl | rfl <;> simp [qPre, preSeq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
  · unfold qTl at h
    rw [loopTl_body qPre 2 qB0 qB1 TEv.idle TEv.idle (by omega)] at h
    have : (i - 2) % 4 = 0 ∨ (i - 2) % 4 = 1 ∨ (i - 2) % 4 = 2 ∨ (i - 2) % 4 = 3 := by omega
    rcases this with h0 | h0 | h0 | h0 <;> rw [h0] at h <;> simp [bAt, qB0, qB1] at h

theorem qno_split : ∀ i a b, qTl i ≠ TEv.splitWrite a b := by
  intro i a b h
  by_cases hi : i < 2
  · unfold qTl at h
    rw [loopTl_pre qPre 2 qB0 qB1 TEv.idle TEv.idle hi] at h
    have : i = 0 ∨ i = 1 := by omega
    rcases this with rfl | rfl <;> simp [qPre, preSeq] at h
  · unfold qTl at h
    rw [loopTl_body qPre 2 qB0 qB1 TEv.idle TEv.idle (by omega)] at h
    have : (i - 2) % 4 = 0 ∨ (i - 2) % 4 = 1 ∨ (i - 2) % 4 = 2 ∨ (i - 2) % 4 = 3 := by omega
    rcases this with h0 | h0 | h0 | h0 <;> rw [h0] at h <;> simp [bAt, qB0, qB1] at h

theorem qno_dma : ∀ i a b, qTl i ≠ TEv.dmaWrite a b := by
  intro i a b h
  by_cases hi : i < 2
  · unfold qTl at h
    rw [loopTl_pre qPre 2 qB0 qB1 TEv.idle TEv.idle hi] at h
    have : i = 0 ∨ i = 1 := by omega
    rcases this with rfl | rfl <;> simp [qPre, preSeq] at h
  · unfold qTl at h
    rw [loopTl_body qPre 2 qB0 qB1 TEv.idle TEv.idle (by omega)] at h
    have : (i - 2) % 4 = 0 ∨ (i - 2) % 4 = 1 ∨ (i - 2) % 4 = 2 ∨ (i - 2) % 4 = 3 := by omega
    rcases this with h0 | h0 | h0 | h0 <;> rw [h0] at h <;> simp [bAt, qB0, qB1] at h

theorem qck (x m : Nat) : qSch.ck x m = 2 + 4 * m + qPos x := rfl


def qCost : Cost := ⟨fun _ => 2, 2, 2⟩

theorem q_wf : WF qSys qCost .L1 .tsc qTl := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    have := loop_prop qPre 2 qB0 qB1 TEv.idle TEv.idle (fun ev => Level.L1.allows .tsc qTl i ev) ?_ ?_ ?_ ?_ ?_ i
    · exact this
    · intro j hj
      have : j = 0 ∨ j = 1 := by omega
      rcases this with rfl | rfl <;> simp [qPre, preSeq, Level.allows, Level.rank]
    · simp [qB0, Level.allows, Level.rank]
    · simp [qB1, Level.allows, Level.rank]
    · simp [Level.allows]
    · simp [Level.allows]
  · intro i
    refine loop_prop qPre 2 qB0 qB1 TEv.idle TEv.idle (fun ev => qCost.admits qSys ev) ?_ ?_ ?_ ?_ ?_ i
    · intro j hj
      have : j = 0 ∨ j = 1 := by omega
      rcases this with rfl | rfl <;> simp [qPre, preSeq, Cost.admits]
    · simp [qB0, Cost.admits, qSys, duoSys]
    · simp [qB1, Cost.admits]
    · simp [Cost.admits]
    · simp [Cost.admits]
  · intro i x e r h a ha hops
    obtain ⟨hi, hc⟩ := qchk i x .honest e r h
    rw [qW i hi]
    rcases hc with ⟨_, rfl, _⟩ | ⟨_, _, hp, _⟩
    · simp [qSys, duoSys] at ha
      simp [wr8, qSys, duoSys]
      omega
    · cases hp
  · intro i x e r h
    obtain ⟨hi, hc⟩ := qchk i x .neutral e r h
    rw [qW i hi]
    rcases hc with ⟨_, _, hp, _⟩ | ⟨_, rfl, _⟩
    · cases hp
    · exact ⟨16, by simp [qSys, duoSys], by simp [qSys, duoSys], by simp [wr8, qSys, duoSys]⟩
  · intro i x med e r h
    obtain ⟨hi, hc⟩ := qchk i x (.mediated med) e r h
    rcases hc with ⟨_, _, hp, _⟩ | ⟨_, _, hp, _⟩ <;> cases hp

theorem q_intact : Intact qSys qTl 0 := by
  apply intact_of_writes
  intro i a b h hc
  obtain ⟨rfl, _⟩ := qwrite i a b h
  simp [qSys, duoSys] at hc

theorem q_a6 : A6 qSys qTl qSch := by
  intro i a b x m0 hw hprot _ hb _ _ _ _ j _
  obtain ⟨rfl, rfl⟩ := qwrite i a b hw
  rw [qck, qW _ (by omega)]
  simp [wr8, qSys, duoSys]

theorem q_a8 : A8 qSys qTl qSch := by
  intro x m e r hx h hex
  rw [qck] at h
  obtain ⟨hi, hc⟩ := qchk _ x .honest e r h
  rcases hc with ⟨h0, rfl, _⟩ | ⟨_, _, hp, _⟩
  · exfalso
    obtain ⟨a, hra, _, hne⟩ := hex
    rw [qck, qW _ hi] at hne
    simp [qSys, duoSys, Sys.inRegion] at hra hne
    simp [wr8] at hne
    omega
  · cases hp

theorem q_noalarm : ¬ Alarm qSys qTl qSch := by
  rintro ⟨x, hx, _, h⟩
  have hx2 : x = 0 ∨ x = 1 := by have : x < 2 := hx; omega
  rcases h with ⟨m, c0, e, r, hc, hnot⟩ | ⟨s, hs⟩
  · rw [qck] at hc hnot
    obtain ⟨hi, hcc⟩ := qchk _ x c0 e r hc
    rcases hcc with ⟨_, rfl, rfl, _⟩ | ⟨_, rfl, rfl, _⟩
    · apply hnot
      rw [qW _ hi]
      apply honest_ok_of_region
      · intro y hy
        simp [qSys, duoSys, Sys.inRegion] at hy
        simp [wr8, qSys, duoSys]
        omega
      · simp [wr8, qSys, duoSys]
    · exact hnot (by simp [checkOk])
  · obtain ⟨c0, e, r, hc, hlt⟩ := hs 0 (by decide)
    rw [Nat.add_zero, qck] at hc
    obtain ⟨_, hcc⟩ := qchk _ x c0 e r hc
    rcases hcc with ⟨_, rfl, _, _, rfl⟩ | ⟨_, rfl, _, _, rfl⟩ <;> simp [qSys, duoSys] at hlt

theorem nec_A2conn : ∃ (C : Cost) (sch : Sched qSys.n qTl),
    WF qSys C .L1 .tsc qTl ∧ AllBut3 14 qSys C qTl sch ∧ Wins qSys qTl sch ∧ ¬ A2conn qSys := by
  refine ⟨qCost, qSch, q_wf, ⟨loop_a1 qPre 2 qB0 qB1 TEv.idle TEv.idle qSys qno_split, ?_, Or.inr ?_, Or.inl rfl,
    ⟨0, by decide, q_intact⟩, duo_A3 _ _ _ _, ?_, ?_, q_a6, Or.inr ?_, q_a8⟩, ⟨⟨1, 16, ?_, ?_, ?_, ?_⟩, q_noalarm⟩, q_no_conn⟩
  · intro a ha
    by_cases h : a < 16
    · exact ⟨0, by decide, (duo_inRegion0 _ _ _ _ _).2 (by simp; omega)⟩
    · exact ⟨1, by decide, (duo_inRegion1 _ _ _ _ _).2 (by simp [qSys, duoSys] at ha ⊢; omega)⟩
  · intro x hx a ha
    by_cases h : x = 0 <;> simp [qSys, duoSys, h] at ha ⊢ <;> omega
  · intro i a b h
    exact qno_dma i a b h
  · intro i x p e r h
    obtain ⟨_, hc⟩ := qchk i x p e r h
    rcases hc with ⟨_, _, _, rfl, rfl⟩ | ⟨_, _, _, rfl, rfl⟩ <;> rfl
  · intro x hx a ha
    by_cases h : x = 0 <;> simp [qSys, duoSys, h] at ha ⊢ <;> omega
  · simp [qTl, loopTl, qPre, preSeq]
  · simp [qSys, duoSys]
  · simp [qSys, duoSys]
  · rw [qW1]
    simp [wr8, qSys, duoSys]


/-! ### A2 (code protected): unit 1's code byte is unprotected, so a modification of it is not covered by persistence

Unit 0 covers unit 1's code and vice versa (the covers graph is strongly connected), but byte 16 of unit 1's code is not protected.
The adversary modifies the protected byte 24 (covered by unit 1 only) and runs unit 1 neutralised: each period it sets byte 16, lets
unit 1 run (neutral), restores byte 16 and lets unit 0 run honestly; unit 0 never sees a modification. -/

def kSys : Sys := duoSys (fun a => a ≠ 16 ∧ a < 32) 24 0 32
def kPre : Nat → TEv := preSeq [TEv.write 24 1, TEv.exec 24]
def kB0 : TEv := TEv.write 16 1
def kB1 : TEv := TEv.check 1 .neutral 1 1
def kB2 : TEv := TEv.write 16 0
def kB3 : TEv := TEv.check 0 .honest 1 1
abbrev kTl : Nat → TEv := loopTl kPre 2 kB0 kB1 kB2 kB3
def kPos : Nat → Nat := fun x => if x = 0 then 3 else 1

abbrev kG : Mem := wr8 Zm 24 1
abbrev kG1 : Mem := wr8 kG 16 1

theorem kG3 : wr8 kG1 16 0 = kG := by
  funext a
  by_cases h : a = 16 <;> simp [wr8, h]

theorem kPre_nc : ∀ i, i < 2 → ∀ x p e r, kPre i ≠ TEv.check x p e r := by
  intro i hi x p e r
  have : i = 0 ∨ i = 1 := by omega
  rcases this with rfl | rfl <;> simp [kPre, preSeq]

def kSch : Sched kSys.n kTl :=
  loopSch kPre 2 kB0 kB1 kB2 kB3 kSys rfl kPos
    (by intro x hx; by_cases h : x = 0 <;> simp [kPos, h])
    (by intro x hx; by_cases h : x = 0
        · subst h; exact ⟨.honest, 1, 1, by simp [kPos, bAt, kB3]⟩
        · have : x = 1 := by omega
          subst this; exact ⟨.neutral, 1, 1, by simp [kPos, bAt, kB1]⟩)
    (by intro j hj x p e r h hx
        have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
        rcases this with rfl | rfl | rfl | rfl <;> simp [bAt, kB0, kB1, kB2, kB3, kPos] at h ⊢ <;>
          first | omega | (obtain ⟨rfl, _⟩ := h; simp) | (obtain ⟨rfl, _⟩ := h; simp [kPos]) )
    kPre_nc

theorem kW2 : worldAt kSys kTl 2 = ⟨kG, kG, false⟩ := by
  simp [worldAt, stepW, kTl, loopTl, kPre, preSeq, World.init, kSys, duoSys]
  rfl

theorem kW1 : worldAt kSys kTl 1 = ⟨kG, kG, false⟩ := by
  simp [worldAt, stepW, kTl, loopTl, kPre, preSeq, World.init, kSys, duoSys]
  rfl

theorem kW : ∀ i, 2 ≤ i → worldAt kSys kTl i =
    if (i - 2) % 4 = 1 ∨ (i - 2) % 4 = 2 then ⟨kG1, kG1, false⟩ else ⟨kG, kG, false⟩ := by
  have hper : stepW (stepW (stepW (stepW (worldAt kSys kTl 2) kB0) kB1) kB2) kB3 = worldAt kSys kTl 2 := by
    rw [kW2]
    simp only [kB0, kB1, kB2, kB3, stepW, step_check]
    simp <;> exact kG3
  intro i hi
  rw [loop_world_mod kPre 2 kB0 kB1 kB2 kB3 kSys hper i hi, kW2]
  have : (i - 2) % 4 = 0 ∨ (i - 2) % 4 = 1 ∨ (i - 2) % 4 = 2 ∨ (i - 2) % 4 = 3 := by omega
  rcases this with h | h | h | h <;> rw [h] <;> simp [loopW, kB0, kB1, kB2, stepW, step_check, kG3] <;>
    first | rfl | exact kG3

theorem kchk : ∀ i x p e r, kTl i = TEv.check x p e r → 2 ≤ i ∧
    (((i - 2) % 4 = 3 ∧ x = 0 ∧ p = .honest ∧ e = 1 ∧ r = 1) ∨ ((i - 2) % 4 = 1 ∧ x = 1 ∧ p = .neutral ∧ e = 1 ∧ r = 1)) := by
  intro i x p e r h
  by_cases hi : i < 2
  · unfold kTl at h
    rw [loopTl_pre kPre 2 kB0 kB1 kB2 kB3 hi] at h
    exact absurd h (kPre_nc i hi x p e r)
  · have hi' : 2 ≤ i := by omega
    refine ⟨hi', ?_⟩
    unfold kTl at h
    rw [loopTl_body kPre 2 kB0 kB1 kB2 kB3 hi'] at h
    have : (i - 2) % 4 = 0 ∨ (i - 2) % 4 = 1 ∨ (i - 2) % 4 = 2 ∨ (i - 2) % 4 = 3 := by omega
    rcases this with h0 | h0 | h0 | h0 <;> rw [h0] at h <;> simp [bAt, kB0, kB1, kB2, kB3] at h
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := h; exact Or.inr ⟨h0, rfl, rfl, rfl, rfl⟩
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := h; exact Or.inl ⟨h0, rfl, rfl, rfl, rfl⟩

/-- Every write is of byte 24 (once, value 1) or of byte 16. -/
theorem kwrite : ∀ i a b, kTl i = TEv.write a b → (a = 24 ∧ b = 1) ∨ a = 16 := by
  intro i a b h
  by_cases hi : i < 2
  · unfold kTl at h
    rw [loopTl_pre kPre 2 kB0 kB1 kB2 kB3 hi] at h
    have : i = 0 ∨ i = 1 := by omega
    rcases this with rfl | rfl <;> simp [kPre, preSeq] at h
    obtain ⟨rfl, rfl⟩ := h; exact Or.inl ⟨rfl, rfl⟩
  · unfold kTl at h
    rw [loopTl_body kPre 2 kB0 kB1 kB2 kB3 (by omega)] at h
    have : (i - 2) % 4 = 0 ∨ (i - 2) % 4 = 1 ∨ (i - 2) % 4 = 2 ∨ (i - 2) % 4 = 3 := by omega
    rcases this with h0 | h0 | h0 | h0 <;> rw [h0] at h <;> simp [bAt, kB0, kB1, kB2, kB3] at h
    · obtain ⟨rfl, _⟩ := h; exact Or.inr rfl
    · obtain ⟨rfl, _⟩ := h; exact Or.inr rfl

theorem kno_split : ∀ i a b, kTl i ≠ TEv.splitWrite a b := by
  intro i a b h
  by_cases hi : i < 2
  · unfold kTl at h
    rw [loopTl_pre kPre 2 kB0 kB1 kB2 kB3 hi] at h
    have : i = 0 ∨ i = 1 := by omega
    rcases this with rfl | rfl <;> simp [kPre, preSeq] at h
  · unfold kTl at h
    rw [loopTl_body kPre 2 kB0 kB1 kB2 kB3 (by omega)] at h
    have : (i - 2) % 4 = 0 ∨ (i - 2) % 4 = 1 ∨ (i - 2) % 4 = 2 ∨ (i - 2) % 4 = 3 := by omega
    rcases this with h0 | h0 | h0 | h0 <;> rw [h0] at h <;> simp [bAt, kB0, kB1, kB2, kB3] at h

theorem kno_dma : ∀ i a b, kTl i ≠ TEv.dmaWrite a b := by
  intro i a b h
  by_cases hi : i < 2
  · unfold kTl at h
    rw [loopTl_pre kPre 2 kB0 kB1 kB2 kB3 hi] at h
    have : i = 0 ∨ i = 1 := by omega
    rcases this with rfl | rfl <;> simp [kPre, preSeq] at h
  · unfold kTl at h
    rw [loopTl_body kPre 2 kB0 kB1 kB2 kB3 (by omega)] at h
    have : (i - 2) % 4 = 0 ∨ (i - 2) % 4 = 1 ∨ (i - 2) % 4 = 2 ∨ (i - 2) % 4 = 3 := by omega
    rcases this with h0 | h0 | h0 | h0 <;> rw [h0] at h <;> simp [bAt, kB0, kB1, kB2, kB3] at h

theorem kck (x m : Nat) : kSch.ck x m = 2 + 4 * m + kPos x := rfl

theorem k_wf : WF kSys qCost .L1 .tsc kTl := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    have := loop_prop kPre 2 kB0 kB1 kB2 kB3 (fun ev => Level.L1.allows .tsc kTl i ev) ?_ ?_ ?_ ?_ ?_ i
    · exact this
    · intro j hj
      have : j = 0 ∨ j = 1 := by omega
      rcases this with rfl | rfl <;> simp [kPre, preSeq, Level.allows, Level.rank]
    · simp [kB0, Level.allows, Level.rank]
    · simp [kB1, Level.allows, Level.rank]
    · simp [kB2, Level.allows, Level.rank]
    · simp [kB3, Level.allows, Level.rank]
  · intro i
    refine loop_prop kPre 2 kB0 kB1 kB2 kB3 (fun ev => qCost.admits kSys ev) ?_ ?_ ?_ ?_ ?_ i
    · intro j hj
      have : j = 0 ∨ j = 1 := by omega
      rcases this with rfl | rfl <;> simp [kPre, preSeq, Cost.admits]
    · simp [kB0, Cost.admits]
    · simp [kB1, Cost.admits]
    · simp [kB2, Cost.admits]
    · simp [kB3, Cost.admits, kSys, duoSys]
  · intro i x e r h a ha hops
    obtain ⟨hi, hc⟩ := kchk i x .honest e r h
    rcases hc with ⟨h3, rfl, _⟩ | ⟨_, _, hp, _⟩
    · rw [kW i hi]
      have : ¬ ((i - 2) % 4 = 1 ∨ (i - 2) % 4 = 2) := by omega
      rw [if_neg this]
      simp [kSys, duoSys] at ha
      simp [wr8, kSys, duoSys]
      omega
    · cases hp
  · intro i x e r h
    obtain ⟨hi, hc⟩ := kchk i x .neutral e r h
    rcases hc with ⟨_, _, hp, _⟩ | ⟨h1, rfl, _⟩
    · cases hp
    · rw [kW i hi, if_pos (Or.inl h1)]
      exact ⟨16, by simp [kSys, duoSys], by simp [kSys, duoSys], by simp [wr8, kSys, duoSys]⟩
  · intro i x med e r h
    obtain ⟨hi, hc⟩ := kchk i x (.mediated med) e r h
    rcases hc with ⟨_, _, hp, _⟩ | ⟨_, _, hp, _⟩ <;> cases hp

theorem k_intact : Intact kSys kTl 0 := by
  apply intact_of_writes
  intro i a b h hc
  rcases kwrite i a b h with ⟨rfl, _⟩ | rfl <;> simp [kSys, duoSys] at hc

theorem k_a6 : A6 kSys kTl kSch := by
  intro i a b x m0 hw hprot _ hb _ _ _ _ j _
  rcases kwrite i a b hw with ⟨rfl, rfl⟩ | rfl
  · rw [kck, kW _ (by omega)]
    split <;> simp [wr8, kSys, duoSys]
  · simp [kSys, duoSys] at hprot

theorem k_a8 : A8 kSys kTl kSch := by
  intro x m e r hx h hex
  rw [kck] at h
  obtain ⟨hi, hc⟩ := kchk _ x .honest e r h
  rcases hc with ⟨h3, rfl, _⟩ | ⟨_, _, hp, _⟩
  · exfalso
    obtain ⟨a, hra, _, hne⟩ := hex
    rw [kck, kW _ hi] at hne
    have : ¬ ((2 + 4 * m + kPos 0 - 2) % 4 = 1 ∨ (2 + 4 * m + kPos 0 - 2) % 4 = 2) := by simp [kPos]; omega
    rw [if_neg this] at hne
    simp [kSys, duoSys, Sys.inRegion] at hra hne
    simp [wr8] at hne
    omega
  · cases hp

theorem k_noalarm : ¬ Alarm kSys kTl kSch := by
  rintro ⟨x, hx, _, h⟩
  rcases h with ⟨m, c0, e, r, hc, hnot⟩ | ⟨s, hs⟩
  · rw [kck] at hc hnot
    obtain ⟨hi, hcc⟩ := kchk _ x c0 e r hc
    rcases hcc with ⟨h3, rfl, rfl, _⟩ | ⟨_, rfl, rfl, _⟩
    · apply hnot
      rw [kW _ hi, if_neg (by omega)]
      apply honest_ok_of_region
      · intro y hy
        simp [kSys, duoSys, Sys.inRegion] at hy
        simp [wr8, kSys, duoSys]
        omega
      · simp [wr8, kSys, duoSys]
    · exact hnot (by simp [checkOk])
  · obtain ⟨c0, e, r, hc, hlt⟩ := hs 0 (by decide)
    rw [Nat.add_zero, kck] at hc
    obtain ⟨_, hcc⟩ := kchk _ x c0 e r hc
    rcases hcc with ⟨_, rfl, _, _, rfl⟩ | ⟨_, rfl, _, _, rfl⟩ <;> simp [kSys, duoSys] at hlt

theorem k_no_code : ¬ A2code kSys := by
  intro h
  have := h 1 (by decide) 16 (by simp [kSys, duoSys])
  simp [kSys, duoSys] at this

theorem nec_A2code : ∃ (C : Cost) (sch : Sched kSys.n kTl),
    WF kSys C .L1 .tsc kTl ∧ AllBut3 13 kSys C kTl sch ∧ Wins kSys kTl sch ∧ ¬ A2code kSys := by
  refine ⟨qCost, kSch, k_wf, ⟨loop_a1 kPre 2 kB0 kB1 kB2 kB3 kSys kno_split, ?_, Or.inl rfl, Or.inr ?_,
    ⟨0, by decide, k_intact⟩, duo_A3 _ _ _ _, ?_, ?_, k_a6, Or.inr ?_, k_a8⟩, ⟨⟨1, 24, ?_, ?_, ?_, ?_⟩, k_noalarm⟩, k_no_code⟩
  · intro a ha
    exact ⟨1, by decide, (duo_inRegion1 _ _ _ _ _).2 (by simp [kSys, duoSys] at ha ⊢; omega)⟩
  · intro x y hx hy
    have hx2 : x = 0 ∨ x = 1 := by have : x < 2 := hx; omega
    have hy2 : y = 0 ∨ y = 1 := by have : y < 2 := hy; omega
    rcases hx2 with rfl | rfl <;> rcases hy2 with rfl | rfl
    · exact Reach.refl hx
    · refine Reach.step (Reach.refl hx) hy ?_
      intro a ha _
      simp [kSys, duoSys, Sys.inRegion] at ha ⊢
      omega
    · refine Reach.step (Reach.refl hx) hy ?_
      intro a ha _
      simp [kSys, duoSys, Sys.inRegion] at ha ⊢
      omega
    · exact Reach.refl hx
  · intro i a b h
    exact kno_dma i a b h
  · intro i x p e r h
    obtain ⟨_, hc⟩ := kchk i x p e r h
    rcases hc with ⟨_, _, _, rfl, rfl⟩ | ⟨_, _, _, rfl, rfl⟩ <;> rfl
  · intro x hx a ha
    by_cases h : x = 0 <;> simp [kSys, duoSys, h] at ha ⊢ <;> omega
  · simp [kTl, loopTl, kPre, preSeq]
  · simp [kSys, duoSys]
  · simp [kSys, duoSys]
  · rw [kW1]
    simp [wr8, kSys, duoSys]

end SmcTamper
