module
public import SmcTamper.Spec.Layout
public import SmcTamper.Bits.Mask

@[expose] public section

namespace SmcTamper

/-! ## Layout arithmetic of §1 and Fig. 5 (C27, C29) -/

theorem perPage_148 : perPage = 148 := by decide
theorem page1_fill : introLen + perPage * unitLen = 4091 := by decide
theorem nopPad_5 : nopPad = 5 := by decide
theorem numUnits_296 : numUnits = 296 := by decide
theorem opOff_first : opOff 0 = 0x60 := by decide

theorem rsiOf_spec (k : Nat) : (k < 148 ∧ rsiOf k = 27 * k) ∨ (148 ≤ k ∧ rsiOf k = 27 * k + 5) := by
  have hp : perPage = 148 := perPage_148
  have hn : nopPad = 5 := nopPad_5
  unfold rsiOf
  rw [hp, hn]
  by_cases h : 148 ≤ k
  · right; simp [h, unitLen]
  · left; simp [h, unitLen]; omega

theorem opOff_page2 (i : Nat) (hi : i < perPage) : opOff (perPage + i) = 4097 + 27 * i := by
  have hp : perPage = 148 := perPage_148
  rw [hp] at *
  have := rsiOf_spec (148 + i)
  simp only [opOff, unitStart, introLen]
  omega

/-- The first unit of page 2 starts at the page boundary. -/
theorem unitStart_page2 : unitStart perPage = pageSize := by decide

/-- Unit starts increase by exactly one unit within a page. -/
theorem opOff_step (k : Nat) (h : k + 1 < numUnits) (hp : k + 1 ≠ perPage) : opOff (k + 1) = opOff k + unitLen := by
  have hp' : perPage = 148 := perPage_148
  rw [hp'] at hp
  have h1 := rsiOf_spec k
  have h2 := rsiOf_spec (k + 1)
  simp only [opOff, unitStart, introLen, unitLen]
  omega

/-- Distinct opcode bytes are at least `unitLen` bytes apart. -/
theorem opOff_sep (i j : Nat) (hij : i < j) (hj : j < numUnits) : opOff i + unitLen ≤ opOff j := by
  have h1 := rsiOf_spec i
  have h2 := rsiOf_spec j
  simp only [opOff, unitStart, introLen, unitLen]
  omega

/-- C27: for every placement of the function (any base address `b`), the 296 opcode bytes lie in 296 distinct aligned
qwords, because they are `27 > 8` bytes apart; so a data read of one qword sees at most one opcode byte. -/
theorem opcode_qwords_distinct (b i j : Nat) (hi : i < numUnits) (hj : j < numUnits) (hne : i ≠ j) :
    (b + opOff i) / 8 ≠ (b + opOff j) / 8 := by
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := opOff_sep i j h hj
    simp only [unitLen] at this; omega
  · have := opOff_sep j i h hi
    simp only [unitLen] at this; omega

/-- The termination patch lands on the byte after `JMP L0` for every unit: `unitStart + 23 + 5 + (7974 − rsi) = 8097`. -/
theorem patch_target (k : Nat) (hk : k < numUnits) : leaOff k + 5 + (patchImm - rsiOf k) = jmpEnd := by
  have h1 := rsiOf_spec k
  have hn : numUnits = 296 := numUnits_296
  rw [hn] at hk
  simp only [leaOff, unitStart, introLen, patchImm, jmpEnd]
  omega

theorem patchImm_ge_rsi (k : Nat) (hk : k < numUnits) : rsiOf k ≤ patchImm := by
  have h1 := rsiOf_spec k
  have hn : numUnits = 296 := numUnits_296
  rw [hn] at hk
  simp only [patchImm]
  omega

theorem patchMask_const : (0xE9#64 ^^^ 0x4808498D48#64) = 0x4808498DA1#64 := by decide

/-- The five patched bytes `48 8D 49 08 48` (a little-endian qword with three zero bytes above) become `E9 disp32`. -/
theorem patch_xor (disp : BitVec 32) :
    0x4808498D48#64 ^^^ patchMask disp = 0xE9#64 ||| (disp.setWidth 64 <<< 8) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [patchMask, BitVec.getLsbD_xor, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  by_cases h8 : i < 8
  · have : (decide (i < 8)) = true := by simpa using h8
    simp [this] <;> (cases (0x4808498D48#64).getLsbD i <;> cases (0xE9#64).getLsbD i <;> simp)
  · have e : (0xE9#64).getLsbD i = false := const_bit_false 0xE9 8 i (by decide) (by omega)
    have : (decide (i < 8)) = false := by simpa using h8
    simp [this, e] <;> (cases (0x4808498D48#64).getLsbD i <;> cases (disp.getLsbD (i - 8)) <;> simp)

/-- Benchmark parameters: `0x8200` bytes. The loop reads `0x8200 / 8 = 4160` qwords; `0x8200 mod 2368 = 128`
(so the final pass has `16` units, the patch index is `15`, and the L04 precondition `size mod 2368 ∉ [1,7]` holds). -/
theorem bench_size_facts :
    0x8200 / 8 = 4160 ∧ 0x8200 % 8 = 0 ∧ 0x8200 % 2368 = 128 ∧ 2368 = 8 * numUnits ∧ (4160 + 295) / 296 = 15 ∧
    4160 % 296 = 16 := by decide

/-- Fig. 5 address arithmetic: `0x7FF7B4521000 + 0x8200 = 0x7FF7B4529200`. -/
theorem fig5_sum : 0x7FF7B4521000 + 0x8200 = 0x7FF7B4529200 := by decide

end SmcTamper
