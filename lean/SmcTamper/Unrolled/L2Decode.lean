module
public import SmcTamper.Unrolled.Main
public import SmcTamper.Layout.Compare
public import SmcTamper.Static.Iter

@[expose] public section

namespace SmcTamper

set_option linter.unusedVariables false

/-! ## Level 2 of the unrolled kernel, part 1: decoding the loop image from memory

`ImgOk enc base M E` says that the loop image sits at `base` in `M` with instructions encoded by `enc` (AsmJit's `encodeA` for
`gen_asm`, MASM's `encode` for `TPCompLoop`), except at the 296 opcode bytes (which the kernel rewrites) and at the offsets in `E`
(the five patched bytes, or the displacement of a self-modified instruction). -/

def ImgOk (enc : Instr → List Nat) (base : Nat) (M : Mem) (E : Nat → Prop) : Prop :=
  ∀ i, i < loopLen → (∀ u, u < 296 → i ≠ opOff u) → ¬ E i → (M (base + i)).toNat = loopAt enc i

/-- The encodings are AsmJit's or MASM's. -/
def EncOk (enc : Instr → List Nat) : Prop := enc = encode ∨ enc = encodeA

/-- Instructions of the loop whose encoding has no displacement field. -/
def constInstrs : List Instr :=
  [.setcc 8 2, .setcc 10 0, .shlB 0 2, .orB 2 0, .shlB 2 3, .leaD 1 1 8, .nop,
   .movRR 7 2, .alu 6 3 3, .aluRI 5 7 2368, .jcc 15 0x4C, .aluRI 0 7 2368, .shiftI 5 7 3, .dec 7, .imulI 6 7 27,
   .aluRI 7 7 148, .jcc 12 3, .aluRI8_32 0 6 5, .movI32 0 7974, .alu 5 0 6, .shiftI 4 0 8,
   .movI64 7 (BitVec.ofNat 64 0x4808498DA1), .alu 6 7 0, .clc, .movStore 8 3]

theorem rt_const (enc : Instr → List Nat) (h : EncOk enc) :
    ∀ i ∈ constInstrs, ∀ t, decodeL (enc i ++ t) = some (i, (enc i).length) := by
  intro i hi t
  simp only [constInstrs, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases h with rfl | rfl <;> rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem rt_xorMB (d : BitVec 32) (t : List Nat) : decodeL (encode (.xorMB d 2) ++ t) = some (.xorMB d 2, 6) := by
  have h : decodeL (encode (.xorMB d 2) ++ t) = some (.xorMB (le32 (d.toNat % 256) (d.toNat / 256 % 256)
      (d.toNat / 65536 % 256) (d.toNat / 16777216 % 256)) 2, 6) := rfl
  rw [h, le32_bytes32]

theorem rt_addMR32 (d : BitVec 32) (t : List Nat) : decodeL (encode (.aluMR32 0 d 6) ++ t) = some (.aluMR32 0 d 6, 6) := by
  have h : decodeL (encode (.aluMR32 0 d 6) ++ t) = some (.aluMR32 0 (le32 (d.toNat % 256) (d.toNat / 256 % 256)
      (d.toNat / 65536 % 256) (d.toNat / 16777216 % 256)) 6, 6) := rfl
  rw [h, le32_bytes32]

theorem rt_subMR32 (d : BitVec 32) (t : List Nat) : decodeL (encode (.aluMR32 5 d 6) ++ t) = some (.aluMR32 5 d 6, 6) := by
  have h : decodeL (encode (.aluMR32 5 d 6) ++ t) = some (.aluMR32 5 (le32 (d.toNat % 256) (d.toNat / 256 % 256)
      (d.toNat / 65536 % 256) (d.toNat / 16777216 % 256)) 6, 6) := rfl
  rw [h, le32_bytes32]

theorem rt_xorMR64 (d : BitVec 32) (t : List Nat) : decodeL (encode (.aluMR64 6 d 7) ++ t) = some (.aluMR64 6 d 7, 7) := by
  have h : decodeL (encode (.aluMR64 6 d 7) ++ t) = some (.aluMR64 6 (le32 (d.toNat % 256) (d.toNat / 256 % 256)
      (d.toNat / 65536 % 256) (d.toNat / 16777216 % 256)) 7, 7) := rfl
  rw [h, le32_bytes32]

theorem rt_jmp32 (d : BitVec 32) (t : List Nat) : decodeL (encode (.jmp32 d) ++ t) = some (.jmp32 d, 5) := by
  have h : decodeL (encode (.jmp32 d) ++ t) = some (.jmp32 (le32 (d.toNat % 256) (d.toNat / 256 % 256)
      (d.toNat / 65536 % 256) (d.toNat / 16777216 % 256)), 5) := rfl
  rw [h, le32_bytes32]

/-- The encodings used by the loop for displacement-carrying instructions are the plain ones in both toolchains. -/
theorem enc_disp (enc : Instr → List Nat) (h : EncOk enc) (d : BitVec 32) :
    enc (.xorMB d 2) = encode (.xorMB d 2) ∧ enc (.aluMR32 0 d 6) = encode (.aluMR32 0 d 6) ∧
    enc (.aluMR32 5 d 6) = encode (.aluMR32 5 d 6) ∧ enc (.aluMR64 6 d 7) = encode (.aluMR64 6 d 7) ∧
    enc (.jmp32 d) = encode (.jmp32 d) ∧ ∀ f, enc (.aluM f 3 1) = encode (.aluM f 3 1) := by
  rcases h with rfl | rfl <;> exact ⟨rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩

theorem decode_of (M : Mem) (A : Nat) (l : List Nat) (i : Instr) (n : Nat) (hn : l.length = n) (hle : n ≤ 10)
    (hl : bytesAt M A n = l) (hr : ∀ t, decodeL (l ++ t) = some (i, n)) : decode M A = some (i, n) := by
  have e : bytesAt M A 10 = bytesAt M A n ++ bytesAt M (A + n) (10 - n) := by
    rw [← bytesAt_add]; congr 1; omega
  unfold decode
  rw [e, hl]
  exact hr _

theorem bytesAt_eq_of (M : Mem) (A : Nat) (l : List Nat) (hl : ∀ k, k < l.length → (M (A + k)).toNat = l.getD k 0) :
    bytesAt M A l.length = l := by
  apply List.ext_getElem
  · simp [bytesAt]
  · intro k h1 h2
    have hk : k < l.length := by simpa [bytesAt] using h1
    simp only [bytesAt, List.getElem_map, List.getElem_range]
    rw [hl k hk]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]

/-- The image bytes are found by position. -/
theorem img_byte (enc : Instr → List Nat) (base : Nat) (M : Mem) (E : Nat → Prop) (hI : ImgOk enc base M E) (i : Nat)
    (hi : i < loopLen) (hop : ∀ u, u < 296 → i ≠ opOff u) (hE : ¬ E i) : (M (base + i)).toNat = loopAt enc i :=
  hI i hi hop hE

/-! ### Bytes of a unit -/

def unitList (enc : Instr → List Nat) (u : Nat) : List Nat := ((unitAt u).map enc).flatten

theorem unitList_len (enc : Instr → List Nat) (h : EncOk enc) (u : Nat) : (unitList enc u).length = 27 := by
  rcases h with rfl | rfl <;> rfl

theorem unitStart_lt (u : Nat) (hu : u < 296) : unitStart u + 27 ≤ 8092 := by
  have := rsiOf_spec u
  simp only [unitStart, introLen]
  omega

theorem loopAt_unit (enc : Instr → List Nat) (u o : Nat) (hu : u < 296) (ho : o < 27) :
    loopAt enc (unitStart u + o) = (unitList enc u).getD o 0 := by
  have hp : perPage = 148 := perPage_148
  have hn : nopPad = 5 := nopPad_5
  unfold loopAt unitList
  rcases Nat.lt_or_ge u 148 with h | h
  · have hn' : ¬ (148 ≤ u) := by omega
    have hs : unitStart u = 95 + 27 * u := by simp [unitStart, rsiOf, hp, hn', introLen, unitLen]
    rw [hs]
    have c1 : ¬ (95 + 27 * u + o < 3) := by omega
    have c2 : ¬ (95 + 27 * u + o < introLen) := by simp only [introLen]; omega
    have c3 : 95 + 27 * u + o < introLen + perPage * unitLen := by simp only [introLen, hp, unitLen]; omega
    rw [if_neg c1, if_neg c2, if_pos c3]
    have e1 : (95 + 27 * u + o - introLen) / unitLen = u := by simp only [introLen, unitLen]; omega
    have e2 : (95 + 27 * u + o - introLen) % unitLen = o := by simp only [introLen, unitLen]; omega
    rw [e1, e2]
  · have hs : unitStart u = 100 + 27 * u := by
      simp only [unitStart, rsiOf, hp, hn, introLen, unitLen]
      rw [if_pos h]; omega
    rw [hs]
    have c1 : ¬ (100 + 27 * u + o < 3) := by omega
    have c2 : ¬ (100 + 27 * u + o < introLen) := by simp only [introLen]; omega
    have c3 : ¬ (100 + 27 * u + o < introLen + perPage * unitLen) := by simp only [introLen, hp, unitLen]; omega
    have c4 : ¬ (100 + 27 * u + o < pageSize) := by simp only [pageSize]; omega
    have c5 : 100 + 27 * u + o < pageSize + perPage * unitLen := by simp only [pageSize, hp, unitLen]; omega
    rw [if_neg c1, if_neg c2, if_neg c3, if_neg c4, if_pos c5]
    have e1 : perPage + (100 + 27 * u + o - pageSize) / unitLen = u := by simp only [pageSize, hp, unitLen]; omega
    have e2 : (100 + 27 * u + o - pageSize) % unitLen = o := by simp only [pageSize, unitLen]; omega
    rw [e1, e2]

/-- A byte of unit `u` other than its opcode byte is never an opcode byte of any unit. -/
theorem notop_unit (u o : Nat) (hu : u < 296) (ho : o < 27) (h1 : o ≠ 1) : ∀ v, v < 296 → unitStart u + o ≠ opOff v := by
  intro v hv e
  have hij : u < v ∨ v < u ∨ v = u := by omega
  rcases hij with h | h | h
  · have := opOff_sep u v h hv
    simp only [opOff, unitLen] at this e
    omega
  · have := opOff_sep v u h hu
    simp only [opOff, unitLen] at this e
    omega
  · subst h; simp only [opOff] at e; omega

theorem unit_byte (enc : Instr → List Nat) (base : Nat) (M : Mem) (E : Nat → Prop) (hI : ImgOk enc base M E) (u o : Nat)
    (hu : u < 296) (ho : o < 27) (h1 : o ≠ 1) (hE : ¬ E (unitStart u + o)) :
    (M (base + (unitStart u + o))).toNat = (unitList enc u).getD o 0 := by
  have := hI (unitStart u + o) (by have := unitStart_lt u hu; rw [loopLen_8123]; omega) (notop_unit u o hu ho h1) hE
  rw [this, loopAt_unit enc u o hu ho]

theorem dec_unit_const (enc : Instr → List Nat) (henc : EncOk enc) (base : Nat) (M : Mem) (E : Nat → Prop)
    (hI : ImgOk enc base M E) (u : Nat) (hu : u < 296) (i : Instr) (hi : i ∈ constInstrs) (o n : Nat)
    (hn : (enc i).length = n) (hon : o + n ≤ 27) (hop : ¬ (o ≤ 1 ∧ 1 < o + n))
    (hE : ∀ k, k < n → ¬ E (unitStart u + o + k)) (hsl : ((unitList enc u).drop o).take n = enc i) (hle : n ≤ 10) :
    decode M (base + unitStart u + o) = some (i, n) := by
  apply decode_of M _ (enc i) i n hn hle
  · have hl : ∀ k, k < (enc i).length → (M (base + unitStart u + o + k)).toNat = (enc i).getD k 0 := by
      intro k hk
      rw [hn] at hk
      have hb := unit_byte enc base M E hI u (o + k) hu (by omega) (by omega) (by rw [← Nat.add_assoc]; exact hE k hk)
      rw [show base + unitStart u + o + k = base + (unitStart u + (o + k)) by omega, hb]
      rw [← hsl]
      have hlen := unitList_len enc henc u
      simp [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop, hk, Nat.add_comm]
    have := bytesAt_eq_of M (base + unitStart u + o) (enc i) hl
    rw [hn] at this
    exact this
  · rw [← hn]; exact rt_const enc henc i hi

/-! ### The eight instructions of a unit -/

section UnitDecode
variable (enc : Instr → List Nat) (henc : EncOk enc) (base : Nat) (M : Mem) (E : Nat → Prop) (hI : ImgOk enc base M E)
  (u : Nat) (hu : u < 296)
include henc hI hu

theorem du_aluM (hE : ∀ o, o < 23 → ¬ E (unitStart u + o)) (hc : IsKernelOpcode (M (base + unitStart u + 1))) :
    decode M (base + unitStart u) =
      some (.aluM (Fin.ofNat 8 (aluField (M (base + unitStart u + 1)))) 3 1, 3) := by
  have b0 := unit_byte enc base M E hI u 0 hu (by omega) (by omega) (hE 0 (by omega))
  have b2 := unit_byte enc base M E hI u 2 hu (by omega) (by omega) (by simpa using hE 2 (by omega))
  have v0 : (unitList enc u).getD 0 0 = 0x48 := by rcases henc with rfl | rfl <;> rfl
  have v2 : (unitList enc u).getD 2 0 = 0x19 := by rcases henc with rfl | rfl <;> rfl
  rw [v0] at b0
  rw [v2] at b2
  simp only [Nat.add_zero] at b0
  apply decode_of M _ [0x48, (M (base + unitStart u + 1)).toNat, 0x19] _ 3 rfl (by omega)
  · have := bytesAt_eq_of M (base + unitStart u) [0x48, (M (base + unitStart u + 1)).toNat, 0x19] (by
      intro k hk
      simp only [List.length_cons, List.length_nil] at hk
      rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
      · simpa using b0
      · rfl
      · rw [show base + unitStart u + 2 = base + (unitStart u + 2) by omega]; simpa using b2)
    simpa using this
  · intro t
    rcases hc with h | h | h | h <;> rw [h] <;> rfl

theorem du_const (i : Instr) (hi : i ∈ constInstrs) (o n : Nat) (hn : (enc i).length = n) (hon : o + n ≤ 27)
    (ho2 : 2 ≤ o) (hle : n ≤ 10) (hE : ∀ k, k < n → ¬ E (unitStart u + o + k))
    (hsl : ((unitList enc u).drop o).take n = enc i) : decode M (base + unitStart u + o) = some (i, n) :=
  dec_unit_const enc henc base M E hI u hu i hi o n hn hon (by omega) hE hsl hle

theorem du_xor (hE : ∀ k, k < 6 → ¬ E (unitStart u + 17 + k)) :
    decode M (base + unitStart u + 17) = some (.xorMB (unitDisp u) 2, 6) := by
  have hn : (enc (.xorMB (unitDisp u) 2)).length = 6 := by rcases henc with rfl | rfl <;> rfl
  have hsl : ((unitList enc u).drop 17).take 6 = enc (.xorMB (unitDisp u) 2) := by rcases henc with rfl | rfl <;> rfl
  apply decode_of M _ (enc (.xorMB (unitDisp u) 2)) _ 6 hn (by omega)
  · have hl : ∀ k, k < (enc (.xorMB (unitDisp u) 2)).length →
        (M (base + unitStart u + 17 + k)).toNat = (enc (.xorMB (unitDisp u) 2)).getD k 0 := by
      intro k hk
      rw [hn] at hk
      have hb := unit_byte enc base M E hI u (17 + k) hu (by omega) (by omega) (by rw [← Nat.add_assoc]; exact hE k hk)
      rw [show base + unitStart u + 17 + k = base + (unitStart u + (17 + k)) by omega, hb, ← hsl]
      have hlen := unitList_len enc henc u
      simp [List.getD_eq_getElem?_getD, List.getElem?_drop, hk]
    have := bytesAt_eq_of M (base + unitStart u + 17) _ hl
    rw [hn] at this
    exact this
  · intro t
    rcases henc with rfl | rfl <;> exact rt_xorMB _ t

end UnitDecode

end SmcTamper
