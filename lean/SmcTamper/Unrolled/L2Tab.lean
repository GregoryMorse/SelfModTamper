module
public import SmcTamper.Unrolled.L2Patch

@[expose] public section

namespace SmcTamper

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Level 2 of the unrolled kernel, part 7: the instructions of the intro and the epilogue, found in the image

Each table entry is (instruction, offset from the function start, encoded length). -/

def introTab : List (Instr × Nat × Nat) :=
  [(.movRR 7 2, 3, 3), (.alu 6 3 3, 6, 3), (.aluRI 5 7 2368, 9, 7), (.jcc 15 0x4C, 16, 2), (.aluRI 0 7 2368, 18, 7),
   (.shiftI 5 7 3, 25, 4), (.dec 7, 29, 3), (.imulI 6 7 27, 32, 4), (.aluRI 7 7 148, 36, 7), (.jcc 12 3, 43, 2),
   (.aluRI8_32 0 6 5, 45, 3), (.movI32 0 7974, 48, 7), (.alu 5 0 6, 55, 3), (.shiftI 4 0 8, 58, 4),
   (.movI64 7 (BitVec.ofNat 64 0x4808498DA1), 62, 10), (.alu 6 7 0, 72, 3), (.aluMR32 0 3 6, 75, 6),
   (.aluMR32 5 (sdisp (-10)) 6, 88, 6), (.clc, 94, 1)]

def tailTab : List (Instr × Nat × Nat) :=
  [(.jmp32 (sdisp (9 - 8097)), 8092, 5), (.aluMR32 0 3 6, 8097, 6), (.aluMR32 5 (sdisp (-10)) 6, 8110, 6),
   (.movStore 8 3, 8116, 3)]

theorem tab_kinds (tab : List (Instr × Nat × Nat)) (h : tab = introTab ∨ tab = tailTab) :
    ∀ p ∈ tab, p.1 ∈ constInstrs ∨ p.1 = .aluMR32 0 3 6 ∨ p.1 = .aluMR32 5 (sdisp (-10)) 6 ∨
      p.1 = .jmp32 (sdisp (9 - 8097)) := by
  rcases h with rfl | rfl <;> decide +kernel

theorem tab_len (enc : Instr → List Nat) (h : EncOk enc) (tab : List (Instr × Nat × Nat)) (ht : tab = introTab ∨ tab = tailTab) :
    ∀ p ∈ tab, (enc p.1).length = p.2.2 := by
  rcases ht with rfl | rfl <;> rcases h with rfl | rfl <;> decide +kernel

theorem tab_sl (enc : Instr → List Nat) (h : EncOk enc) (tab : List (Instr × Nat × Nat)) (ht : tab = introTab ∨ tab = tailTab) :
    ∀ p ∈ tab, ∀ k, k < p.2.2 → loopAt enc (p.2.1 + k) = (enc p.1).getD k 0 := by
  rcases ht with rfl | rfl <;> rcases h with rfl | rfl <;> decide +kernel

theorem introTab_pos : ∀ p ∈ introTab, 3 ≤ p.2.1 ∧ p.2.1 + p.2.2 ≤ 95 ∧ p.2.2 ≤ 10 := by decide +kernel
theorem tailTab_pos : ∀ p ∈ tailTab, 8092 ≤ p.2.1 ∧ p.2.1 + p.2.2 ≤ 8123 ∧ p.2.2 ≤ 10 := by decide +kernel

theorem tab_rt (enc : Instr → List Nat) (h : EncOk enc) (tab : List (Instr × Nat × Nat)) (ht : tab = introTab ∨ tab = tailTab) :
    ∀ p ∈ tab, ∀ t, decodeL (enc p.1 ++ t) = some (p.1, p.2.2) := by
  intro p hp t
  have hl := tab_len enc h tab ht p hp
  rcases tab_kinds tab ht p hp with hc | h1 | h2 | h3
  · have := rt_const enc h p.1 hc t
    rwa [hl] at this
  · rw [h1] at hl ⊢
    rw [← hl]
    rcases h with rfl | rfl <;> exact rt_addMR32 3 t
  · rw [h2] at hl ⊢
    rw [← hl]
    rcases h with rfl | rfl <;> exact rt_subMR32 _ t
  · rw [h3] at hl ⊢
    rw [← hl]
    rcases h with rfl | rfl <;> exact rt_jmp32 _ t

theorem intro_dec (enc : Instr → List Nat) (henc : EncOk enc) (base : Nat) (M : Mem) (E : Nat → Prop)
    (hI : ImgOk enc base M E) (hE : ∀ i, 3 ≤ i → i < 95 → ¬ E i) :
    ∀ p ∈ introTab, decode M (base + p.2.1) = some (p.1, p.2.2) := by
  intro p hp
  have hpos := introTab_pos p hp
  exact dec_intro enc henc base M E hI p.1 p.2.1 p.2.2 (tab_len enc henc introTab (Or.inl rfl) p hp) (by omega)
    (by omega) (fun k hk => hE _ (by omega) (by omega)) (tab_sl enc henc introTab (Or.inl rfl) p hp)
    (tab_rt enc henc introTab (Or.inl rfl) p hp)

theorem tail_dec (enc : Instr → List Nat) (henc : EncOk enc) (base : Nat) (M : Mem) (E : Nat → Prop)
    (hI : ImgOk enc base M E) (hE : ∀ i, 8092 ≤ i → i < 8123 → ¬ E i) :
    ∀ p ∈ tailTab, decode M (base + p.2.1) = some (p.1, p.2.2) := by
  intro p hp
  have hpos := tailTab_pos p hp
  exact dec_tail enc henc base M E hI p.1 p.2.1 p.2.2 (tab_len enc henc tailTab (Or.inr rfl) p hp) (by omega)
    (by omega) (by omega) (fun k hk => hE _ (by omega) (by omega)) (tab_sl enc henc tailTab (Or.inr rfl) p hp)
    (tab_rt enc henc tailTab (Or.inr rfl) p hp)

/-- The bytes of a table instruction are the bytes of its encoding. -/
theorem tab_bytes (enc : Instr → List Nat) (henc : EncOk enc) (base : Nat) (M : Mem) (E : Nat → Prop)
    (hI : ImgOk enc base M E) (tab : List (Instr × Nat × Nat)) (ht : tab = introTab ∨ tab = tailTab)
    (hE : ∀ p ∈ tab, ∀ k, k < p.2.2 → ¬ E (p.2.1 + k)) (hop : ∀ p ∈ tab, ∀ k, k < p.2.2 → ∀ u, u < 296 → p.2.1 + k ≠ opOff u) :
    ∀ p ∈ tab, bytesAt M (base + p.2.1) p.2.2 = enc p.1 := by
  intro p hp
  have hl := tab_len enc henc tab ht p hp
  have hpos : p.2.1 + p.2.2 ≤ 8123 ∧ (p.2.1 + p.2.2 ≤ 95 ∨ 8092 ≤ p.2.1) := by
    rcases ht with rfl | rfl
    · have := introTab_pos p hp; omega
    · have := tailTab_pos p hp; omega
  have := bytesAt_eq_of M (base + p.2.1) (enc p.1) (by
    intro k hk
    rw [hl] at hk
    rw [show base + p.2.1 + k = base + (p.2.1 + k) by omega,
      hI (p.2.1 + k) (by rw [loopLen_8123]; omega) (hop p hp k hk) (hE p hp k hk),
      tab_sl enc henc tab ht p hp k hk])
  rwa [hl] at this

theorem hop_intro : ∀ p ∈ introTab, ∀ k, k < p.2.2 → ∀ u, u < 296 → p.2.1 + k ≠ opOff u := by
  intro p hp k hk u hu
  have := introTab_pos p hp
  have := opOff_ge u
  omega

theorem hop_tail : ∀ p ∈ tailTab, ∀ k, k < p.2.2 → ∀ u, u < 296 → p.2.1 + k ≠ opOff u := by
  intro p hp k hk u hu
  have := tailTab_pos p hp
  have := opOff_lt u hu
  omega

end SmcTamper
