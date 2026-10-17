module
public import SmcTamper.Spec.Paper
public import SmcTamper.Threat.T3full
public import SmcTamper.Threat.SplitMirror
public import SmcTamper.Threat.Matrix
public import SmcTamper.Harvard.Separation

@[expose] public section

namespace SmcTamper.Paper

theorem security_theorem : SecurityTheorem := fun S C l t tl sch hwf hA => security S C l t tl sch hwf hA

theorem othersHold_of_allBut {i : Nat} {S : Sys} {C : Cost} {tl : Nat → TEv} {sch : Sched S.n tl}
    (h : AllBut i S C tl sch) : OthersHold i S C tl sch := by
  obtain ⟨h1, h2, h2c, h2n, h12, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, Or.inr h2c, Or.inr h2n, h12, h3, h4, h5, h6, Or.inr h7, h8⟩

theorem othersHold_of_allBut3 {i : Nat} {S : Sys} {C : Cost} {tl : Nat → TEv} {sch : Sched S.n tl}
    (h : AllBut3 i S C tl sch) : OthersHold i S C tl sch := by
  obtain ⟨h1, h2, h2c, h2n, h12, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨Or.inr h1, Or.inr h2, h2c, h2n, Or.inr h12, Or.inr h3, Or.inr h4, Or.inr h5, Or.inr h6, h7, Or.inr h8⟩

theorem necessary_old {i : Nat} (hN : Necessary i) (hi : i = 1 ∨ i = 2 ∨ i = 12 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 8) :
    NecessaryAssumption i := by
  obtain ⟨S, C, l, t, tl, sch, hwf, hall, hw, hn⟩ := hN
  refine ⟨S, C, l, t, tl, sch, hwf, ?_, hw, ?_⟩
  · obtain ⟨h1, h2, h2c, h2n, h12, h3, h4, h5, h6, h7, h8⟩ := hall
    exact ⟨h1, h2, Or.inr h2c, Or.inr h2n, h12, h3, h4, h5, h6, Or.inr h7, h8⟩
  · rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hn

theorem necessary_new {i : Nat} (hN : Necessary3 i) (hi : i = 7 ∨ i = 13 ∨ i = 14) : NecessaryAssumption i := by
  obtain ⟨S, C, l, t, tl, sch, hwf, hall, hw, hn⟩ := hN
  refine ⟨S, C, l, t, tl, sch, hwf, othersHold_of_allBut3 hall, hw, ?_⟩
  rcases hi with rfl | rfl | rfl <;> exact hn

theorem assumptions_necessary : AssumptionsNecessary := by
  obtain ⟨⟨n1, n2, n12, n3, n4, n5, n6, n8⟩, n7, n13, n14⟩ := T3_full
  exact ⟨necessary_old n1 (by omega), necessary_old n2 (by omega), necessary_old n3 (by omega),
    necessary_old n4 (by omega), necessary_old n5 (by omega), necessary_old n6 (by omega),
    necessary_new n7 (by omega), necessary_old n8 (by omega), necessary_old n12 (by omega),
    necessary_new n13 (by omega), necessary_new n14 (by omega)⟩

theorem faithful_iff (opAddr : Nat) (med : Nat → Bool) : ∀ (n i : Nat) (s : VState),
    FaithfulRun opAddr med i n s ↔ Faithful opAddr med i n s := by
  intro n
  induction n with
  | zero => intro i s; simp [FaithfulRun, Faithful]
  | succ n ih => intro i s; simp only [FaithfulRun, Faithful, ih]

theorem mediation_theorem : MediationTheorem := by
  refine ⟨fun opAddr med n i s hf j hj ht => faithful_needs_med opAddr med n i s ((faithful_iff opAddr med n i s).1 hf) j hj ht, ?_⟩
  intro S C tl hA3 hA5 c x med e r hx hev hadm s0 hf j hj ht
  exact mediated_timefail S C tl hA3 hA5 c x med e r hx hev hadm s0 ((faithful_iff _ med _ 0 s0).1 hf) j hj ht

theorem level_matrix : LevelMatrix := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := T4
  refine ⟨fun S C l tl hwf hr => ?_, ?_, ?_, ?_, ?_⟩
  · exact h0 S C l tl hwf hr
  · obtain ⟨C, sch, a, o, b, c⟩ := h1; exact ⟨_, C, _, sch, a, othersHold_of_allBut o, b, c⟩
  · obtain ⟨C, sch, a, o, b, c⟩ := h2; exact ⟨_, C, _, sch, a, othersHold_of_allBut o, b, c⟩
  · obtain ⟨C, sch, a, o, b, c⟩ := h3; exact ⟨_, C, _, sch, a, othersHold_of_allBut o, b, c⟩
  · obtain ⟨C, sch, a, o, b, c⟩ := h4; exact ⟨_, C, _, sch, a, othersHold_of_allBut o, b, c⟩

theorem harvard_separation : HarvardSeparation := by
  intro C S Obs H V emb N obsH obsV hsim s m
  exact ⟨fun a ha => harvard_reads_sensitive H V emb N obsH obsV hsim s m a ha,
    fun ss hnd hss ρ tV tH hT => harvard_time_bound H V emb N obsH obsV hsim s m ss hnd hss ρ tV tH hT⟩

end SmcTamper.Paper
