module
public import SmcTamper.Unrolled.Level1

@[expose] public section

namespace SmcTamper

set_option linter.unusedVariables false

/-! ## The `adjustOffsets` map of `TPCompCLoop` and the data read of the self-modified image -/

theorem opOff_lit1 (i : Nat) (hi : i < 148) : opOff i = 0x60 + 0x1b * i := by
  have h := rsiOf_spec i
  simp only [opOff, unitStart, introLen]
  omega

theorem opOff_lit2 (i : Nat) (hi : i < 148) : opOff (148 + i) = 4097 + 0x1b * i := by
  have h := opOff_page2 i (by rw [perPage_148]; exact hi)
  rw [perPage_148] at h
  rw [h]

def entryOf (base i : Nat) : Nat × Nat × Nat := ((base + opOff i) / 8 * 8, (base + opOff i) % 8, i)

theorem adjustEntries_mem (base : Nat) (e : Nat × Nat × Nat) :
    e ∈ adjustEntries base ↔ ∃ i, i < 296 ∧ e = entryOf base i := by
  simp only [adjustEntries, List.mem_append, List.mem_map, List.mem_range]
  constructor
  · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · refine ⟨i, by omega, ?_⟩
      simp only [entryOf, opOff_lit1 i hi]
      rw [show base + (0x60 + 0x1b * i) = base + 0x60 + 0x1b * i by omega]
    · refine ⟨148 + i, by omega, ?_⟩
      simp only [entryOf, opOff_lit2 i hi]
      rw [show base + (4097 + 0x1b * i) = base + 4097 + 0x1b * i by omega, show i + 148 = 148 + i by omega]
  · rintro ⟨i, hi, rfl⟩
    by_cases h1 : i < 148
    · left; refine ⟨i, h1, ?_⟩
      simp only [entryOf, opOff_lit1 i h1]
      rw [show base + (0x60 + 0x1b * i) = base + 0x60 + 0x1b * i by omega]
    · right; refine ⟨i - 148, by omega, ?_⟩
      have : i = 148 + (i - 148) := by omega
      have e2 := opOff_lit2 (i - 148) (by omega)
      rw [← this] at e2
      simp only [entryOf, e2]
      rw [show base + (4097 + 0x1b * (i - 148)) = base + 4097 + 0x1b * (i - 148) by omega, show i - 148 + 148 = i by omega]

theorem key_inj (base i j : Nat) (hi : i < 296) (hj : j < 296) (h : (base + opOff i) / 8 * 8 = (base + opOff j) / 8 * 8) :
    i = j := by
  by_cases hne : i = j
  · exact hne
  · exact absurd (by omega) (opcode_qwords_distinct base i j hi hj hne)

theorem adjustFind_some (base p bi idx : Nat) (h : adjustFind base p = some (bi, idx)) :
    idx < 296 ∧ p = (base + opOff idx) / 8 * 8 ∧ bi = (base + opOff idx) % 8 := by
  unfold adjustFind at h
  cases hf : (adjustEntries base).find? (fun e => e.1 == p) with
  | none => simp [hf] at h
  | some e =>
    simp [hf] at h
    have hm := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    obtain ⟨i, hi, rfl⟩ := (adjustEntries_mem base e).1 hm
    simp only [entryOf, beq_iff_eq] at hp
    simp only [entryOf, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    subst h2
    exact ⟨hi, hp.symm, h1.symm⟩

theorem adjustFind_none (base p : Nat) (h : adjustFind base p = none) :
    ∀ u, u < 296 → p ≠ (base + opOff u) / 8 * 8 := by
  intro u hu hp
  unfold adjustFind at h
  cases hf : (adjustEntries base).find? (fun e => e.1 == p) with
  | some e => simp [hf] at h
  | none =>
    have := List.find?_eq_none.1 hf (entryOf base u) ((adjustEntries_mem base _).2 ⟨u, hu, rfl⟩)
    simp [entryOf, hp] at this

theorem adjustFind_hit (base u : Nat) (hu : u < 296) :
    adjustFind base ((base + opOff u) / 8 * 8) = some ((base + opOff u) % 8, u) := by
  unfold adjustFind
  cases hf : (adjustEntries base).find? (fun e => e.1 == (base + opOff u) / 8 * 8) with
  | none =>
    have := List.find?_eq_none.1 hf (entryOf base u) ((adjustEntries_mem base _).2 ⟨u, hu, rfl⟩)
    simp [entryOf] at this
  | some e =>
    have hm := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    obtain ⟨i, hi, rfl⟩ := (adjustEntries_mem base e).1 hm
    simp only [entryOf, beq_iff_eq] at hp
    have : i = u := key_inj base i u hi hu hp
    subst this
    simp [entryOf]

/-- Two distinct opcode bytes are never in the same aligned qword window of 8 bytes. -/
theorem opaddr_window (base u v a : Nat) (hu : u < 296) (hv : v < 296) (huv : u ≠ v)
    (h1 : a ≤ base + opOff u) (h2 : base + opOff u < a + 8) (h3 : a ≤ base + opOff v) (h4 : base + opOff v < a + 8) : False := by
  rcases Nat.lt_or_gt_of_ne huv with h | h
  · have := opOff_sep u v h hv; simp only [unitLen] at this; omega
  · have := opOff_sep v u h hu; simp only [unitLen] at this; omega

/-- The data read of the self-modified image: the C substitution of `TPCompCLoop` (`adjustOffsets`, `preserve`). -/
theorem rd64_opsMem (base : Nat) (m : Mem) (ops : Nat → Nat) (p : Nat)
    (hK : ∀ u, u < 296 → IsKernelOpcode (m (base + opOff u))) (hops : ∀ u, u < 296 → IsOp (ops u)) (hp : p % 8 = 0) :
    rd64 (opsMem base m ops) p =
      (match adjustFind base p with
       | some (bi, idx) => cSubst (rd64 m p) bi (ops idx)
       | none => rd64 m p) := by
  cases hf : adjustFind base p with
  | none =>
    have hn := adjustFind_none base p hf
    apply rd64_congr
    intro k hk
    apply opsMem_other
    intro u hu e
    apply hn u hu
    omega
  | some r =>
    obtain ⟨bi, idx⟩ := r
    obtain ⟨hidx, hpe, hbi⟩ := adjustFind_some base p bi idx hf
    have hb : base + opOff idx = p + bi := by omega
    have e1 : rd64 (opsMem base m ops) p = rd64 (wr8 m (base + opOff idx) (opcodeOf (ops idx))) p := by
      apply rd64_congr
      intro k hk
      by_cases hk' : p + k = base + opOff idx
      · rw [hk', opsMem_at base m ops idx hidx]; simp [wr8]
      · have : wr8 m (base + opOff idx) (opcodeOf (ops idx)) (p + k) = m (p + k) := by simp [wr8, hk']
        rw [this]
        apply opsMem_other
        intro u hu e
        by_cases huv : u = idx
        · subst huv; exact hk' e
        · exact opaddr_window base u idx p hu hidx huv (by omega) (by omega) (by omega) (by omega)
    rw [e1, hpe, rd64_wr8_aligned]
    have hx : IsKernelOpcode (byteAt (rd64 m p) bi) := by
      rw [byteAt_rd64 m p bi (by omega), ← hb]; exact hK idx hidx
    rw [← hpe]
    show _ = cSubst (rd64 m p) bi (ops idx)
    rw [cSubst_eq_setByte (rd64 m p) bi (by omega) (ops idx) (hops idx hidx) hx, ← hbi]

end SmcTamper
