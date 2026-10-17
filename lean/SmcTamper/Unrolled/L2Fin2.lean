module
public import SmcTamper.Unrolled.L2Fin1

@[expose] public section

namespace SmcTamper

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Level 2 of the unrolled kernel, part 12: the patched final unit and the epilogue -/

/-- The eight bytes at the patch address (the five patched bytes and the three after them). -/
def E0 (w : Nat) : Nat → Prop := fun i => leaOff w ≤ i ∧ i < leaOff w + 8

/-- The first `w` units, then the first seven instructions of unit `w`, whose `LEA` the patch has turned into a jump to
the epilogue. -/
theorem patched_run (enc : Instr → List Nat) (henc : EncOk enc) (base : Nat) (s : St) (K : KState) (w : Nat)
    (hw : w ≤ 294) (h147 : w ≠ 147) (hrip : s.rip = base + 95) (hcf : s.fl.cf = false) (hR : Rel s K)
    (hb : K.ptr + 8 * (w + 1) < 2 ^ 63) (hI : ImgOk enc base s.mem (E0 w))
    (hK : ∀ v, v < 296 → IsKernelOpcode (s.mem (base + opOff v)))
    (hjb : bytesAt s.mem (base + leaOff w) 5 = encode (.jmp32 (BitVec.ofNat 32 (patchImm - rsiOf w)))) :
    ∃ N sj, run N s = some sj ∧ sj.rip = base + 8097 ∧
      sj.regs 3 = (unitStep base w (unitsFrom base 0 w K)).sum ∧
      sj.mem = (unitStep base w (unitsFrom base 0 w K)).mem ∧
      (∀ i : Fin 16, i.val ≠ 0 → i.val ≠ 1 → i.val ≠ 2 → i.val ≠ 3 → sj.regs i = s.regs i) ∧
      ImgOk enc base sj.mem (E0 w) := by
  have p0 := pos_spec 0
  have hw' : w < 296 := by omega
  have q4 := unitStart_eq_pos w hw'
  obtain ⟨su, e1, r1, c1, R1, g1, I1, K1⟩ := units_chain enc henc base (E0 w) w 0 s K (by omega)
    (by rw [hrip]; omega) hcf hR (by omega) hI hK
    (fun i h1 h2 h => by
      have : pos (0 + w) = unitStart w := by rw [Nat.zero_add]; exact q4.symm
      simp only [E0, leaOff] at h; omega)
  have hbo : ∀ x, (x = base + leaOff w + 0 ∨ x = base + leaOff w + 1 ∨ x = base + leaOff w + 2 ∨ x = base + leaOff w + 3 ∨
      x = base + leaOff w + 4) → ∀ v, v < 296 → x ≠ base + opOff v := by
    intro x hx v hv e
    have h1 := patch_not_opcode (w + 1) v 0 (by omega) (by omega) hv (by omega)
    have h2 := patch_not_opcode (w + 1) v 1 (by omega) (by omega) hv (by omega)
    have h3 := patch_not_opcode (w + 1) v 2 (by omega) (by omega) hv (by omega)
    have h4 := patch_not_opcode (w + 1) v 3 (by omega) (by omega) hv (by omega)
    have h5 := patch_not_opcode (w + 1) v 4 (by omega) (by omega) hv (by omega)
    simp only [Nat.add_sub_cancel] at h1 h2 h3 h4 h5
    omega
  -- the five bytes are unchanged by the units so far
  have hbs : bytesAt su.mem (base + leaOff w) 5 = bytesAt s.mem (base + leaOff w) 5 := by
    apply bytesAt_congr
    intro k hk
    rw [R1.mem, unitsFrom_mem_out base _ (hbo _ (by omega)) w 0 K, hR.mem]
  have hptr : (su.regs 1).toNat = (unitsFrom base 0 w K).ptr := by
    rw [R1.ptr, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by rw [unitsFrom_ptr]; omega)
  have hk := kstate_ext_of (unitsFrom base 0 w K) su.mem (su.regs 1).toNat (su.regs 3) R1.mem.symm hptr.symm R1.sum.symm
  have hEu : ∀ o, o < 23 → ¬ E0 w (unitStart w + o) := by
    intro o ho h; simp only [E0, leaOff] at h; omega
  obtain ⟨s7, e7, r7, c7, sum7, mem7, g7⟩ := unit7 enc henc base (E0 w) su w hw' (by rw [r1, Nat.zero_add, q4]) c1 I1 hEu K1
  rw [hk] at sum7 mem7
  have hI7 := imgOk_unit enc base su.mem (E0 w) I1 K1 w (unitsFrom base 0 w K) R1.mem.symm
  rw [← mem7] at hI7
  -- the jump
  have hbs7 : bytesAt s7.mem (base + leaOff w) 5 = bytesAt s.mem (base + leaOff w) 5 := by
    rw [← hbs]
    apply bytesAt_congr
    intro k hk
    rw [mem7]
    have := unitsFrom_mem_out base (base + leaOff w + k) (hbo _ (by omega)) 1 w (unitsFrom base 0 w K)
    have e : unitsFrom base w 1 (unitsFrom base 0 w K) = unitStep base w (unitsFrom base 0 w K) := rfl
    rw [e] at this
    rw [this, ← R1.mem]
  have dd : decode s7.mem s7.rip = some (.jmp32 (BitVec.ofNat 32 (patchImm - rsiOf w)), 5) := by
    have hr : s7.rip = base + leaOff w := by rw [r7]; simp only [leaOff]; omega
    rw [hr]
    apply decode_of s7.mem _ (encode (.jmp32 (BitVec.ofNat 32 (patchImm - rsiOf w)))) _ 5 (by simp [encode, bytes32]) (by omega)
    · rw [hbs7]; exact hjb
    · intro t; exact rt_jmp32 _ t
  have st := step_of_decode s7 _ _ dd
  have hs := rsiOf_spec w
  have hpt := patch_target w (by rw [numUnits_296]; omega)
  have hpi : patchImm = 7974 := rfl
  have hji : jmpEnd = 8097 := rfl
  refine ⟨steps 0 w + (7 + 1), exec (.jmp32 (BitVec.ofNat 32 (patchImm - rsiOf w))) 5 s7, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [run_add, e1]
    simp only [Option.bind_some]
    rw [run_add, e7]
    simp only [Option.bind_some]
    rw [run_one, st]
  · show (Int.ofNat (s7.rip + 5) + (BitVec.ofNat 32 (patchImm - rsiOf w)).toInt).toNat = _
    rw [toInt_ofNat32 _ (by omega), r7]
    simp only [Int.ofNat_eq_natCast]
    simp only [leaOff, jmpEnd, unitStart, introLen] at hpt ⊢
    omega
  · exact sum7
  · exact mem7
  · intro i h0 h1 h2 h3
    show s7.regs i = _
    rw [g7 i h0 h2 h3, g1 i h0 h1 h2 h3]
  · exact hI7.1

/-- The epilogue: the same patch again (restoring the five bytes), then the store of the sum. -/
theorem epilogue_run (enc : Instr → List Nat) (henc : EncOk enc) (base : Nat) (s : St) (w : Nat) (hw : w ≤ 294)
    (hrip : s.rip = base + 8097) (h6 : s.regs 6 = BitVec.ofNat 64 (rsiOf w)) (hI : ImgOk enc base s.mem (E0 w)) :
    ∃ N sf, run N s = some sf ∧ sf.rip = base + 8119 ∧
      sf.mem = wr64 (xorQword s.mem (base + leaOff w) (s.regs 7)) (s.regs 8).toNat (s.regs 3) ∧
      (∀ i, sf.regs i = s.regs i) := by
  have hs := rsiOf_spec w
  have hs0 := rsiOf_spec 0
  have hE : ∀ p ∈ tailTab, ∀ k, k < p.2.2 → ¬ E0 w (p.2.1 + k) := by
    intro p hp k hk h
    have := tailTab_pos p hp
    simp only [E0, leaOff, unitStart, introLen] at h
    omega
  have hbytes := tab_bytes enc henc base s.mem (E0 w) hI tailTab (Or.inr rfl) hE hop_tail
  have hq := loopAt_xorq_tail enc henc
  have hte := tab_encode enc henc
  have hbA := hbytes (.aluMR32 0 3 6, 8097, 6) (by decide)
  have hbS := hbytes (.aluMR32 5 (sdisp (-10)) 6, 8110, 6) (by decide)
  simp only [] at hbA hbS
  rw [hte.1] at hbA
  rw [hte.2] at hbS
  have img : ∀ i, 8103 ≤ i → i < 8110 → (s.mem (base + i)).toNat = loopAt enc i := by
    intro i h1 h2
    refine hI i (by rw [loopLen_8123]; omega) (fun u hu => ?_) (fun h => ?_)
    · have := opOff_lt u hu; omega
    · simp only [E0, leaOff, unitStart, introLen] at h; omega
  have hdisp : rd32 s.mem (base + 8097 + 9) = sdisp ((leaOff 0 : Int) - 8110) := by
    apply rd32_of_bytes
    intro j hj
    rw [show base + 8097 + 9 + j = base + (8106 + j) by omega, img (8106 + j) (by omega) (by omega), hq.2.2.2 j hj]
  obtain ⟨s3, e3, r3, m3, g3⟩ := patch3 base 8097 s ((leaOff 0 : Int) - 8110) (rsiOf w) (base + leaOff w) hrip
    hbA
    (by rw [show base + 8097 + 6 = base + 8103 by omega, img 8103 (by omega) (by omega), hq.1])
    (by rw [show base + 8097 + 6 + 1 = base + 8104 by omega, img 8104 (by omega) (by omega), hq.2.1])
    (by rw [show base + 8097 + 6 + 2 = base + 8105 by omega, img 8105 (by omega) (by omega), hq.2.2.1])
    hdisp (by rw [show base + 8097 + 13 = base + 8110 by omega]; exact hbS) h6 (by omega)
    (by simp only [leaOff, unitStart, introLen, Int.ofNat_eq_natCast]; omega)
    (by simp only [leaOff, unitStart, introLen, Int.ofNat_eq_natCast]; omega)
    (by simp only [leaOff, unitStart, introLen, Int.ofNat_eq_natCast]; omega)
    (by simp only [leaOff, unitStart, introLen]; omega) (by simp only [leaOff, unitStart, introLen]; omega)
  have hI3 : ImgOk enc base s3.mem (E0 w) := by
    rw [m3]
    exact imgOk_mono enc base _ _ _ (imgOk_win enc base s.mem (E0 w) (leaOff w) (s.regs 7) hI)
      (fun i h => by rcases h with h | h <;> exact h)
  have d4 : decode s3.mem s3.rip = some (.movStore 8 3, 3) := by
    rw [r3, show base + 8097 + 19 = base + 8116 by omega]
    exact tail_dec enc henc base s3.mem (E0 w) hI3 (fun i h1 h2 h => by simp only [E0, leaOff, unitStart, introLen] at h; omega)
      (.movStore 8 3, 8116, 3) (by decide)
  have st4 := step_of_decode s3 _ _ d4
  refine ⟨3 + 1, exec (.movStore 8 3) 3 s3, ?_, ?_, ?_, ?_⟩
  · rw [run_add, e3]
    simp only [Option.bind_some]
    rw [run_one, st4]
  · show s3.rip + 3 = _
    rw [r3]
  · show wr64 s3.mem (s3.regs 8).toNat (s3.regs 3) = _
    rw [m3, g3 8, g3 3]
  · intro i
    show s3.regs i = _
    rw [g3 i]

end SmcTamper
