module
public import SmcTamper.Threat.Forgery
public import SmcTamper.Threat.Matrix

@[expose] public section

namespace SmcTamper

/-! ## Levels are ordered by capability; L3 adds no event kind to L2

A hypervisor (L3) can trap `RDTSC`, offset the TSC and use EPT permissions (R-class facts, `THREAT_MODEL.md` section 4); in the event
model these are the forged readings (`Level.forgesReading`) and the mediated check path, which L2 already has.  So an L3 adversary has
exactly the events of an L2 one, and the model's L3 is a name for the point where the platform contract (not the event set) changes. -/

theorem allows_mono (l l' : Level) (h : l.rank ≤ l'.rank) (t : TimerSrc) (tl : Nat → TEv) (i : Nat) (ev : TEv)
    (hl : l ≠ .L0) : l.allows t tl i ev → l'.allows t tl i ev := by
  intro ha
  cases ev with
  | exec a => trivial
  | idle => trivial
  | regWrite => simp only [Level.allows] at ha ⊢; omega
  | write a b =>
    simp only [Level.allows] at ha ⊢
    rcases ha with ha | ⟨h0, _⟩
    · exact Or.inl (by omega)
    · exact absurd h0 hl
  | splitWrite a b => simp only [Level.allows] at ha ⊢; omega
  | dmaWrite a b => simp only [Level.allows] at ha ⊢; omega
  | check x p e r =>
    simp only [Level.allows, Level.forgesReading] at ha ⊢
    obtain ⟨h1, h2⟩ := ha
    refine ⟨?_, ?_⟩
    · rcases h1 with h1 | h1
      · exact Or.inl h1
      · right; cases t <;> simp only [Level.forgesReading] at h1 ⊢ <;> omega
    · cases p <;> simp only at h2 ⊢ <;> omega

/-- **L3 = L2 on events.** -/
theorem L3_events_eq_L2 (t : TimerSrc) (tl : Nat → TEv) (i : Nat) (ev : TEv) :
    Level.L3.allows t tl i ev ↔ Level.L2.allows t tl i ev := by
  cases ev <;> simp [Level.allows, Level.forgesReading, Level.rank] <;> cases t <;> simp [Level.forgesReading, Level.rank]

end SmcTamper
