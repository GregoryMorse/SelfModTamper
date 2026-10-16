module
public import SmcTamper.Spec.Kernel
public import SmcTamper.Spec.CModel
public import SmcTamper.Layout.Numbers
public import SmcTamper.Static.Emulation

@[expose] public section

namespace SmcTamper

set_option linter.unusedVariables false

/-! ## Memory with 296 self-modified opcode bytes

`opsMem base m ops` is the image `m` with the opcode byte of unit `u` (at `base + opOff u`) replaced by `opcodeOf (ops u)`. -/

open Classical in
noncomputable def opsMem (base : Nat) (m : Mem) (ops : Nat → Nat) : Mem := fun a =>
  if h : ∃ u, u < numUnits ∧ a = base + opOff u then opcodeOf (ops (Classical.choose h)) else m a

theorem opOff_inj (u v : Nat) (hu : u < numUnits) (hv : v < numUnits) (h : opOff u = opOff v) : u = v := by
  rcases Nat.lt_trichotomy u v with h1 | h1 | h1
  · have := opOff_sep u v h1 hv; simp only [unitLen] at this; omega
  · exact h1
  · have := opOff_sep v u h1 hu; simp only [unitLen] at this; omega

theorem opsMem_at (base : Nat) (m : Mem) (ops : Nat → Nat) (u : Nat) (hu : u < numUnits) :
    opsMem base m ops (base + opOff u) = opcodeOf (ops u) := by
  unfold opsMem
  have h : ∃ w, w < numUnits ∧ base + opOff u = base + opOff w := ⟨u, hu, rfl⟩
  rw [dif_pos h]
  have := (Classical.choose_spec h)
  have e : Classical.choose h = u := opOff_inj _ _ this.1 hu (by omega)
  rw [e]

theorem opsMem_other (base : Nat) (m : Mem) (ops : Nat → Nat) (a : Nat)
    (h : ∀ u, u < numUnits → a ≠ base + opOff u) : opsMem base m ops a = m a := by
  unfold opsMem
  rw [dif_neg]
  rintro ⟨u, hu, e⟩
  exact h u hu e

theorem opsMem_self (base : Nat) (m : Mem) (ops : Nat → Nat) (h : ∀ u, u < numUnits → m (base + opOff u) = opcodeOf (ops u)) :
    opsMem base m ops = m := by
  funext a
  by_cases ha : ∃ u, u < numUnits ∧ a = base + opOff u
  · obtain ⟨u, hu, rfl⟩ := ha
    rw [opsMem_at base m ops u hu, h u hu]
  · rw [opsMem_other]
    intro u hu e; exact ha ⟨u, hu, e⟩

/-- Writing the toggled opcode byte of unit `v` updates the op array at `v`. -/
theorem opsMem_upd (base : Nat) (m : Mem) (ops : Nat → Nat) (v x : Nat) (hv : v < numUnits) :
    wr8 (opsMem base m ops) (base + opOff v) (opcodeOf x) = opsMem base m (fun i => if i = v then x else ops i) := by
  funext a
  by_cases ha : ∃ u, u < numUnits ∧ a = base + opOff u
  · obtain ⟨u, hu, rfl⟩ := ha
    rw [opsMem_at base m _ u hu]
    by_cases huv : u = v
    · subst huv; simp [wr8]
    · have : opOff u ≠ opOff v := fun e => huv (opOff_inj _ _ hu hv e)
      simp [wr8, this, opsMem_at base m ops u hu, huv]
  · have h1 : ∀ u, u < numUnits → a ≠ base + opOff u := fun u hu e => ha ⟨u, hu, e⟩
    have : a ≠ base + opOff v := h1 v hv
    simp [wr8, this, opsMem_other base m _ a h1]

theorem rd64_congr (m1 m2 : Mem) (p : Nat) (h : ∀ k, k < 8 → m1 (p + k) = m2 (p + k)) : rd64 m1 p = rd64 m2 p := by
  unfold rd64
  have h0 := h 0 (by omega)
  rw [Nat.add_zero] at h0
  rw [h0, h 1 (by omega), h 2 (by omega), h 3 (by omega), h 4 (by omega), h 5 (by omega), h 6 (by omega),
    h 7 (by omega)]

end SmcTamper
