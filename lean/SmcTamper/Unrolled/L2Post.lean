module
public import SmcTamper.Unrolled.L2Intro

@[expose] public section

namespace SmcTamper

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Level 2 of the unrolled kernel, part 10: the termination patch of the intro -/

theorem patchImm_7974 : patchImm = 7974 := rfl

theorem imgOk_win (enc : Instr → List Nat) (base : Nat) (M : Mem) (E : Nat → Prop) (pa : Nat) (v : BitVec 64)
    (hI : ImgOk enc base M E) : ImgOk enc base (xorQword M (base + pa) v) (fun i => E i ∨ (pa ≤ i ∧ i < pa + 8)) := by
  intro i hi hop hE'
  have h1 : ¬ E i := fun h => hE' (Or.inl h)
  have h2 : ¬ (pa ≤ i ∧ i < pa + 8) := fun h => hE' (Or.inr h)
  unfold xorQword
  have : ¬ (base + pa ≤ base + i ∧ base + i < base + pa + 8) := by omega
  rw [if_neg this]
  exact hI i hi hop h1

/-- The rest of the intro after `rsi` is set: build the patch word in `rdi`, run the self-modifying triple, `clc`. -/
theorem intro_post (enc : Instr → List Nat) (henc : EncOk enc) (base : Nat) (s : St) (E : Nat → Prop) (w : Nat)
    (hw : w < 296) (hrip : s.rip = base + 48) (h6 : s.regs 6 = BitVec.ofNat 64 (rsiOf w))
    (hI : ImgOk enc base s.mem E) (hE : ∀ i, 3 ≤ i → i < 95 → ¬ E i) :
    ∃ s', run 9 s = some s' ∧ s'.rip = base + 95 ∧ s'.fl.cf = false ∧
      s'.mem = xorQword s.mem (base + leaOff w) (patchVal (w + 1)) ∧ s'.regs 7 = patchVal (w + 1) ∧
      s'.regs 6 = s.regs 6 ∧ (∀ i : Fin 16, i.val ≠ 0 → i.val ≠ 7 → s'.regs i = s.regs i) := by
  have dec := intro_dec enc henc base s.mem E hI hE
  have hrs := rsiOf_spec w
  have hrs' : rsiOf w ≤ 7970 := by omega
  -- mov rax, 7974
  have d1 : decode s.mem s.rip = some (.movI32 0 7974, 7) := by
    rw [hrip]; exact dec (.movI32 0 7974, 48, 7) (by decide)
  obtain ⟨s1, st1, r1, m1, v1, g1⟩ := regstep_run s _ _ _ _ rs_movrax d1
  -- sub rax, rsi
  have d2 : decode s1.mem s1.rip = some (.alu 5 0 6, 3) := by
    rw [m1, r1, hrip]; exact dec (.alu 5 0 6, 55, 3) (by decide)
  obtain ⟨s2, st2, r2, m2, v2, g2⟩ := regstep_run s1 _ _ _ _ rs_subrax d2
  -- shl rax, 8
  have d3 : decode s2.mem s2.rip = some (.shiftI 4 0 8, 4) := by
    rw [m2, m1, r2, r1, hrip]; exact dec (.shiftI 4 0 8, 58, 4) (by decide)
  obtain ⟨s3, st3, r3, m3, v3, g3⟩ := regstep_run s2 _ _ _ _ rs_shlrax d3
  -- mov rdi, imm64
  have d4 : decode s3.mem s3.rip = some (.movI64 7 (BitVec.ofNat 64 0x4808498DA1), 10) := by
    rw [m3, m2, m1, r3, r2, r1, hrip]; exact dec (.movI64 7 (BitVec.ofNat 64 0x4808498DA1), 62, 10) (by decide)
  obtain ⟨s4, st4, r4, m4, v4, g4⟩ := regstep_run s3 _ _ _ _ rs_movrdi d4
  -- xor rdi, rax
  have d5 : decode s4.mem s4.rip = some (.alu 6 7 0, 3) := by
    rw [m4, m3, m2, m1, r4, r3, r2, r1, hrip]; exact dec (.alu 6 7 0, 72, 3) (by decide)
  obtain ⟨s5, st5, r5, m5, v5, g5⟩ := regstep_run s4 _ _ _ _ rs_xorrdi d5
  -- values
  have hrax : s2.regs 0 = BitVec.ofNat 64 (7974 - rsiOf w) := by
    rw [v2, v1, g1 6 (by decide), h6]
    exact ofNat_sub64 7974 (rsiOf w) (by omega) (by omega)
  have hrax3 : s3.regs 0 = BitVec.ofNat 64 (7974 - rsiOf w) <<< 8 := by rw [v3, hrax]
  have hrdi : s5.regs 7 = patchVal (w + 1) := by
    rw [v5, v4, g4 0 (by decide), hrax3]
    show _ = patchMask (BitVec.ofNat 32 (patchImm - rsiOf (w + 1 - 1)))
    rw [show w + 1 - 1 = w by omega, patchImm_7974]
    exact xor_patch _ (by omega)
  -- the self-modifying triple
  have hbytes := tab_bytes enc henc base s.mem E hI introTab (Or.inl rfl)
    (fun p hp k hk => hE _ (by have := introTab_pos p hp; omega) (by have := introTab_pos p hp; omega)) hop_intro
  have hm5 : s5.mem = s.mem := by rw [m5, m4, m3, m2, m1]
  have hr5 : s5.rip = base + 75 := by rw [r5, r4, r3, r2, r1, hrip]
  have hrs6 : s5.regs 6 = BitVec.ofNat 64 (rsiOf w) := by
    rw [g5 6 (by decide), g4 6 (by decide), g3 6 (by decide), g2 6 (by decide), g1 6 (by decide), h6]
  have hq := loopAt_xorq enc henc
  have hte := tab_encode enc henc
  have hbA := hbytes (.aluMR32 0 3 6, 75, 6) (by decide)
  have hbS := hbytes (.aluMR32 5 (sdisp (-10)) 6, 88, 6) (by decide)
  simp only [] at hbA hbS
  rw [hte.1] at hbA
  rw [hte.2] at hbS
  have img : ∀ i, 81 ≤ i → i < 88 → (s.mem (base + i)).toNat = loopAt enc i := by
    intro i h1 h2
    exact hI i (by rw [loopLen_8123]; omega) (fun u hu => by have := opOff_ge u; omega) (hE i (by omega) (by omega))
  have hdisp : rd32 s5.mem (base + 75 + 9) = sdisp 30 := by
    rw [hm5]
    apply rd32_of_bytes
    intro j hj
    rw [show base + 75 + 9 + j = base + (84 + j) by omega, img (84 + j) (by omega) (by omega), hq.2.2.2 j hj]
  obtain ⟨s8, e8, r8, m8, g8⟩ := patch3 base 75 s5 30 (rsiOf w) (base + leaOff w) hr5
    (by rw [hm5]; exact hbA)
    (by rw [hm5, show base + 75 + 6 = base + 81 by omega, img 81 (by omega) (by omega), hq.1])
    (by rw [hm5, show base + 75 + 6 + 1 = base + 82 by omega, img 82 (by omega) (by omega), hq.2.1])
    (by rw [hm5, show base + 75 + 6 + 2 = base + 83 by omega, img 83 (by omega) (by omega), hq.2.2.1])
    hdisp (by rw [hm5]; exact hbS) hrs6 (by omega) (by omega) (by omega)
    (by simp only [leaOff, unitStart, introLen, Int.ofNat_eq_natCast]; omega)
    (by simp only [leaOff, unitStart, introLen]; omega) (by simp only [leaOff, unitStart, introLen]; omega)
  -- clc
  have hI8 := imgOk_win enc base s.mem E (leaOff w) (s5.regs 7) hI
  have hE8 : ∀ i, 3 ≤ i → i < 95 → ¬ (E i ∨ (leaOff w ≤ i ∧ i < leaOff w + 8)) := by
    intro i h1 h2 h
    rcases h with h | h
    · exact hE i h1 h2 h
    · simp only [leaOff, unitStart, introLen] at h; omega
  rw [← hm5, ← m8] at hI8
  have d9 : decode s8.mem s8.rip = some (.clc, 1) := by
    rw [r8, show base + 75 + 19 = base + 94 by omega]
    exact intro_dec enc henc base s8.mem _ hI8 hE8 (.clc, 94, 1) (by decide)
  have st9 := step_of_decode s8 _ _ d9
  have h9 := exec_clc 1 s8
  generalize exec .clc 1 s8 = s9 at h9 st9
  have hrun : run 9 s = some s9 := by
    rw [run_succ_some 8 s s1 st1, run_succ_some 7 s1 s2 st2, run_succ_some 6 s2 s3 st3, run_succ_some 5 s3 s4 st4,
      run_succ_some 4 s4 s5 st5]
    have e3 : run 3 s5 = some s8 := e8
    rw [show (4 : Nat) = 3 + 1 from rfl, run_add, e3]
    simp only [Option.bind_some]
    rw [run_one, st9]
  refine ⟨s9, hrun, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h9]; show s8.rip + 1 = _; rw [r8]
  · rw [h9]
  · rw [h9]; show s8.mem = _; rw [m8, hm5, hrdi]
  · rw [h9]; show s8.regs 7 = _; rw [g8 7, hrdi]
  · rw [h9]; show s8.regs 6 = _; rw [g8 6, hrs6, h6]
  · intro i h0 h7
    rw [h9]; show s8.regs i = _
    rw [g8 i, g5 i (fun e => h7 (by rw [e]; rfl)), g4 i (fun e => h7 (by rw [e]; rfl)), g3 i (fun e => h0 (by rw [e]; rfl)),
      g2 i (fun e => h0 (by rw [e]; rfl)), g1 i (fun e => h0 (by rw [e]; rfl))]

end SmcTamper
