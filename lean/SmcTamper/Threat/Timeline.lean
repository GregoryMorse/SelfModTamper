module
public import SmcTamper.Spec.Threat
public import SmcTamper.Bits.Bytes

@[expose] public section

namespace SmcTamper

/-! ## View invariants of a timeline -/

/-- Without view separation the fetch view and the data view are one image. -/
theorem coherent_eq (S : Sys) (tl : Nat → TEv) (h1 : ∀ n, (worldAt S tl n).split = false) :
    ∀ n, (worldAt S tl n).F = (worldAt S tl n).D := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    have hs := h1 (n + 1)
    simp only [worldAt] at hs ⊢
    cases e : tl n with
    | write a b => simp only [e, stepW]; rw [ih]
    | dmaWrite a b => simp only [e, stepW]; rw [ih]
    | splitWrite a b => simp only [e, stepW] at hs; exact absurd hs (by decide)
    | exec _ => simp only [e, stepW]; exact ih
    | check _ _ _ _ => simp only [e, stepW]; exact ih
    | regWrite => simp only [e, stepW]; exact ih
    | idle => simp only [e, stepW]; exact ih

/-- Without view separation and physical writers, the only way the fetch view differs from the image is a modifying `write`. -/
theorem last_write (S : Sys) (tl : Nat → TEv) (h1 : ∀ n, (worldAt S tl n).split = false) (h4 : ∀ i a b, tl i ≠ TEv.dmaWrite a b)
    (a : Nat) : ∀ n, (worldAt S tl n).F a ≠ S.I0 a → ∃ i b, i < n ∧ tl i = TEv.write a b ∧ b ≠ S.I0 a := by
  intro n
  induction n with
  | zero => intro h; exact absurd rfl h
  | succ n ih =>
    intro h
    have hs := h1 (n + 1)
    simp only [worldAt] at h hs
    cases e : tl n with
    | write a' b =>
      simp only [e, stepW, wr8] at h
      by_cases hx : a = a'
      · subst hx
        simp only [ite_true] at h
        exact ⟨n, b, Nat.lt_succ_self n, e, h⟩
      · simp only [hx, ite_false] at h
        obtain ⟨i, b', hi, hti, hb⟩ := ih h
        exact ⟨i, b', by omega, hti, hb⟩
    | splitWrite a' b => simp only [e, stepW] at hs; cases hs
    | dmaWrite a' b => exact absurd e (h4 n a' b)
    | exec _ => simp only [e, stepW] at h; obtain ⟨i, b', hi, hti, hb⟩ := ih h; exact ⟨i, b', by omega, hti, hb⟩
    | check _ _ _ _ => simp only [e, stepW] at h; obtain ⟨i, b', hi, hti, hb⟩ := ih h; exact ⟨i, b', by omega, hti, hb⟩
    | regWrite => simp only [e, stepW] at h; obtain ⟨i, b', hi, hti, hb⟩ := ih h; exact ⟨i, b', by omega, hti, hb⟩
    | idle => simp only [e, stepW] at h; obtain ⟨i, b', hi, hti, hb⟩ := ih h; exact ⟨i, b', by omega, hti, hb⟩

/-- An intact unit's code (outside the opcode bytes) is always the original. -/
theorem intact_code_orig (S : Sys) (tl : Nat → TEv) (h1 : ∀ n, (worldAt S tl n).split = false)
    (h4 : ∀ i a b, tl i ≠ TEv.dmaWrite a b) (x : Nat) (hx : Intact S tl x) (a : Nat)
    (hc : (S.unit x).code a) (ho : ¬ S.ops a) (n : Nat) : (worldAt S tl n).F a = S.I0 a := by
  refine Classical.byContradiction ?_
  intro hne
  obtain ⟨i, b, _, hti, hb⟩ := last_write S tl h1 h4 a n hne
  exact hx ⟨i, a, b, hti, hc, ho, hb⟩

/-- A modification persists in the data view exactly as in the fetch view (coherent worlds). -/
theorem coherent_D_eq_F (S : Sys) (tl : Nat → TEv) (h1 : ∀ n, (worldAt S tl n).split = false) (n a : Nat) :
    (worldAt S tl n).D a = (worldAt S tl n).F a := by
  rw [coherent_eq S tl h1 n]

/-! ### The two-view kernel agrees with the Level-1 kernel on a coherent image -/

theorem vRun_coherent (opAddr : Nat) :
    ∀ (n i : Nat) (D : Mem) (p : Nat) (sm : BitVec 64),
      (vRun opAddr (fun _ => true) i n ⟨D, D, p, sm⟩).F = (vRun opAddr (fun _ => true) i n ⟨D, D, p, sm⟩).D ∧
      (vRun opAddr (fun _ => true) i n ⟨D, D, p, sm⟩).sum = (staticRun opAddr n ⟨D, p, sm⟩).sum ∧
      (vRun opAddr (fun _ => true) i n ⟨D, D, p, sm⟩).D = (staticRun opAddr n ⟨D, p, sm⟩).mem := by
  intro n
  induction n with
  | zero => intro i D p sm; exact ⟨rfl, rfl, rfl⟩
  | succ n ih =>
    intro i D p sm
    simp only [vRun, staticRun]
    exact ih (i + 1) _ _ _

/-- C21-style link: on one coherent image the two-view value is the Level-1 value of the reset image. -/
theorem coherent_viewValue (cu : CheckUnit) (D : Mem) :
    viewValue cu true D D (fun _ => true) = cu.value (cu.reset D) := by
  unfold viewValue CheckUnit.value CheckUnit.run CheckUnit.reset
  simp only [ite_true]
  obtain ⟨_, h2, h3⟩ := vRun_coherent cu.opAddr (cu.size / 8) 0 (wr8 D cu.opAddr cu.canon) cu.start 0
  rw [h2, h3]

end SmcTamper
