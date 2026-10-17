module
public import SmcTamper.Unrolled.L2Arith

@[expose] public section

namespace SmcTamper

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Level 2 of the unrolled kernel, part 9: the setup, the passes and the final intro -/

theorem fin8_val4 : (4 : Fin 8).val = 4 := rfl
theorem fin8_val6 : (6 : Fin 8).val = 6 := rfl

theorem run_two (s s1 s2 : St) (e1 : step s = some s1) (e2 : step s1 = some s2) : run 2 s = some s2 := by
  rw [run_succ_some 1 s s1 e1, run_succ_some 0 s1 s2 e2]; rfl

/-- `mov rdi, rdx; xor rbx, rbx`. -/
theorem head_run (enc : Instr → List Nat) (henc : EncOk enc) (base : Nat) (s : St) (size : Nat)
    (hrip : s.rip = base + 3) (h2 : s.regs 2 = BitVec.ofNat 64 size) (hI : ImgOk enc base s.mem (fun _ => False)) :
    ∃ s', run 2 s = some s' ∧ s'.rip = base + 9 ∧ s'.regs 7 = BitVec.ofNat 64 size ∧ s'.regs 3 = 0 ∧ s'.mem = s.mem ∧
      (∀ i : Fin 16, i.val ≠ 3 → i.val ≠ 7 → s'.regs i = s.regs i) := by
  have d1 : decode s.mem s.rip = some (.movRR 7 2, 3) := by
    rw [hrip]; exact intro_dec enc henc base s.mem _ hI (fun i _ _ h => h) (.movRR 7 2, 3, 3) (by decide)
  have st1 := step_of_decode s _ _ d1
  have r1 : (exec (.movRR 7 2) 3 s).rip = base + 6 := by show s.rip + 3 = _; rw [hrip]
  have m1 : (exec (.movRR 7 2) 3 s).mem = s.mem := rfl
  have g1 : ∀ i : Fin 16, i ≠ 7 → (exec (.movRR 7 2) 3 s).regs i = s.regs i := by
    intro i hi; simp [exec, St.setReg, hi]
  have v1 : (exec (.movRR 7 2) 3 s).regs 7 = s.regs 2 := by simp [exec, St.setReg]
  generalize exec (.movRR 7 2) 3 s = s1 at r1 m1 g1 v1 st1
  have d2 : decode s1.mem s1.rip = some (.alu 6 3 3, 3) := by
    rw [m1, r1]; exact intro_dec enc henc base s.mem _ hI (fun i _ _ h => h) (.alu 6 3 3, 6, 3) (by decide)
  have st2 := step_of_decode s1 _ _ d2
  have r2 : (exec (.alu 6 3 3) 3 s1).rip = base + 9 := by show s1.rip + 3 = _; rw [r1]
  have m2 : (exec (.alu 6 3 3) 3 s1).mem = s.mem := by show s1.mem = _; exact m1
  have g2 : ∀ i : Fin 16, i ≠ 3 → (exec (.alu 6 3 3) 3 s1).regs i = s1.regs i := by
    intro i hi; simp [exec, St.setReg, hi]
  have v2 : (exec (.alu 6 3 3) 3 s1).regs 3 = 0 := by
    simp [exec, St.setReg, aluW, fin8_val6]
  generalize exec (.alu 6 3 3) 3 s1 = s2 at r2 m2 g2 v2 st2
  refine ⟨s2, run_two s s1 s2 st1 st2, r2, ?_, v2, m2, ?_⟩
  · rw [g2 7 (by decide), v1, h2]
  · intro i h3 h7
    rw [g2 i (fun e => h3 (by rw [e]; rfl)), g1 i (fun e => h7 (by rw [e]; rfl))]

theorem toNat_ofNat64_small (n : Nat) (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem unitsFrom_ptr (base : Nat) : ∀ (n u : Nat) (k : KState), (unitsFrom base u n k).ptr = k.ptr + 8 * n := by
  intro n
  induction n with
  | zero => intro u k; rfl
  | succ n ih =>
    intro u k
    show (unitsFrom base ((u + 1) % numUnits) n (unitStep base u k)).ptr = _
    rw [ih]
    show k.ptr + 8 + 8 * n = _
    omega

theorem fullPasses_ptr (base : Nat) : ∀ (q : Nat) (k : KState), (fullPasses base q k).ptr = k.ptr + 2368 * q := by
  intro q
  induction q with
  | zero => intro k; rfl
  | succ q ih =>
    intro k
    show (fullPasses base q (unitsFrom base 0 numUnits k)).ptr = _
    rw [ih, unitsFrom_ptr, numUnits_296]
    omega

set_option maxRecDepth 8192 in
/-- `q` full passes. -/
theorem passes_run (enc : Instr → List Nat) (henc : EncOk enc) (base : Nat) :
    ∀ (q : Nat) (s : St) (k : KState), s.rip = base + 9 → 2368 * q < (s.regs 7).toNat → (s.regs 7).toNat < 2 ^ 63 →
      Rel s k → k.ptr + 2368 * q < 2 ^ 63 → ImgOk enc base s.mem (fun _ => False) →
      (∀ v, v < 296 → IsKernelOpcode (s.mem (base + opOff v))) →
      ∃ s', run (passLen * q) s = some s' ∧ s'.rip = base + 9 ∧ (s'.regs 7).toNat = (s.regs 7).toNat - 2368 * q ∧
        Rel s' (fullPasses base q k) ∧
        (∀ i : Fin 16, i.val ≠ 0 → i.val ≠ 1 → i.val ≠ 2 → i.val ≠ 3 → i.val ≠ 7 → s'.regs i = s.regs i) ∧
        ImgOk enc base s'.mem (fun _ => False) ∧ (∀ v, v < 296 → IsKernelOpcode (s'.mem (base + opOff v))) := by
  intro q
  induction q with
  | zero =>
    intro s k hrip h1 h2 hR hb hI hK
    exact ⟨s, by simp [run], hrip, by simp, hR, fun _ _ _ _ _ _ => rfl, hI, hK⟩
  | succ q ih =>
    intro s k hrip h1 h2 hR hb hI hK
    rw [Nat.mul_add_one] at h1 hb
    have a1 : 2368 < (s.regs 7).toNat := by clear ih hI hK hR hrip; omega
    have a2 : k.ptr + 2368 < 2 ^ 63 := by clear ih hI hK hR hrip; omega
    obtain ⟨s1, e1, r1, v1, R1, g1, I1, K1⟩ := pass_run enc henc base s k hrip a1 h2 hR a2 hI hK
    have t1 : (s1.regs 7).toNat = (s.regs 7).toNat - 2368 := by
      rw [v1]; exact toNat_sub2368 _ (by omega)
    have hb1 : (unitsFrom base 0 296 k).ptr = k.ptr + 2368 := by
      rw [unitsFrom_ptr]
    obtain ⟨s', e', r', v', R', g', I', K'⟩ := ih s1 (unitsFrom base 0 296 k) r1 (by omega) (by omega) R1
      (by rw [hb1]; omega) I1 K1
    refine ⟨s', ?_, r', ?_, ?_, ?_, I', K'⟩
    · rw [show passLen * (q + 1) = passLen + passLen * q by rw [Nat.mul_succ, Nat.add_comm], run_add, e1]
      exact e'
    · rw [v', t1]; omega
    · show Rel s' (fullPasses base q (unitsFrom base 0 numUnits k))
      rw [numUnits_296]; exact R'
    · intro i h0 h1' h2' h3 h7
      rw [g' i h0 h1' h2' h3 h7, g1 i h0 h1' h2' h3 h7]


def RegStep (i : Instr) (len : Nat) (r : Fin 16) (f : St → BitVec 64) : Prop :=
  ∀ s : St, (exec i len s).rip = s.rip + len ∧ (exec i len s).mem = s.mem ∧ (exec i len s).regs r = f s ∧
    ∀ j, j ≠ r → (exec i len s).regs j = s.regs j

theorem regstep_run (s : St) (i : Instr) (len : Nat) (r : Fin 16) (f : St → BitVec 64) (h : RegStep i len r f)
    (d : decode s.mem s.rip = some (i, len)) :
    ∃ s1, step s = some s1 ∧ s1.rip = s.rip + len ∧ s1.mem = s.mem ∧ s1.regs r = f s ∧ ∀ j, j ≠ r → s1.regs j = s.regs j := by
  obtain ⟨a, b, c, e⟩ := h s
  exact ⟨_, step_of_decode s i len d, a, b, c, e⟩

theorem rs_addrdi : RegStep (.aluRI 0 7 2368) 7 7 (fun s => s.regs 7 + 2368) := by
  intro s
  obtain ⟨a, b, c, d, e⟩ := exec_aluRI_facts 0 7 2368 7 s (by decide)
  refine ⟨a, b, ?_, e⟩
  rw [d, sext2368]; rfl

theorem rs_shr : RegStep (.shiftI 5 7 3) 4 7 (fun s => s.regs 7 >>> 3) := by
  intro s
  refine ⟨rfl, rfl, ?_, ?_⟩
  · simp [exec, shiftW, St.setReg, fin8_val5]
  · intro j hj; simp [exec, St.setReg, hj]

theorem rs_dec : RegStep (.dec 7) 3 7 (fun s => s.regs 7 - 1) := by
  intro s
  refine ⟨rfl, rfl, ?_, ?_⟩
  · simp [exec, St.setReg]
  · intro j hj; simp [exec, St.setReg, hj]

theorem rs_imul : RegStep (.imulI 6 7 27) 4 6 (fun s => BitVec.ofInt 64 ((s.regs 7).toInt * (27 : BitVec 8).toInt)) := by
  intro s
  refine ⟨rfl, rfl, ?_, ?_⟩
  · simp [exec, St.setReg]
  · intro j hj; simp [exec, St.setReg, hj]

theorem rs_add32 : RegStep (.aluRI8_32 0 6 5) 3 6
    (fun s => ((s.regs 6).setWidth 32 + (5 : BitVec 8).signExtend 32).setWidth 64) := by
  intro s
  refine ⟨rfl, rfl, ?_, ?_⟩
  · simp [exec, St.setReg, aluW]
  · intro j hj; simp [exec, St.setReg, hj]

theorem rs_movrax : RegStep (.movI32 0 7974) 7 0 (fun s => 7974) := by
  intro s
  refine ⟨rfl, rfl, ?_, ?_⟩
  · simp [exec, St.setReg, sext7974]
  · intro j hj; simp [exec, St.setReg, hj]

theorem rs_subrax : RegStep (.alu 5 0 6) 3 0 (fun s => s.regs 0 - s.regs 6) := by
  intro s
  refine ⟨rfl, rfl, ?_, ?_⟩
  · simp [exec, St.setReg, aluW]
  · intro j hj; simp [exec, St.setReg, hj]

theorem rs_shlrax : RegStep (.shiftI 4 0 8) 4 0 (fun s => s.regs 0 <<< 8) := by
  intro s
  refine ⟨rfl, rfl, ?_, ?_⟩
  · simp [exec, shiftW, St.setReg, fin8_val4]
  · intro j hj; simp [exec, St.setReg, hj]

theorem rs_movrdi : RegStep (.movI64 7 (BitVec.ofNat 64 0x4808498DA1)) 10 7 (fun s => BitVec.ofNat 64 0x4808498DA1) := by
  intro s
  refine ⟨rfl, rfl, ?_, ?_⟩
  · simp [exec, St.setReg]
  · intro j hj; simp [exec, St.setReg, hj]

theorem rs_xorrdi : RegStep (.alu 6 7 0) 3 7 (fun s => s.regs 7 ^^^ s.regs 0) := by
  intro s
  refine ⟨rfl, rfl, ?_, ?_⟩
  · simp [exec, St.setReg, aluW, fin8_val6]
  · intro j hj; simp [exec, St.setReg, hj]


theorem exec_cmpRI_facts (r : Fin 16) (imm : BitVec 32) (len : Nat) (s : St) :
    (exec (.aluRI 7 r imm) len s).rip = s.rip + len ∧ (exec (.aluRI 7 r imm) len s).mem = s.mem ∧
    (exec (.aluRI 7 r imm) len s).regs = s.regs ∧
    (exec (.aluRI 7 r imm) len s).fl = (aluW 7 (s.regs r) (imm.signExtend 64) s.fl.cf).2 := ⟨rfl, rfl, rfl, rfl⟩

theorem toNat2368 : (2368 : BitVec 64).toNat = 2368 := by decide
theorem toNat148 : (BitVec.signExtend 64 (148 : BitVec 32)).toNat = 148 := by decide +kernel
theorem sext148 : (BitVec.signExtend 64 (148 : BitVec 32)) = 148 := by decide +kernel

theorem intro_pre (enc : Instr → List Nat) (henc : EncOk enc) (base : Nat) (s : St) (E : Nat → Prop)
    (hrip : s.rip = base + 9) (hR1 : 8 ≤ (s.regs 7).toNat) (hR2 : (s.regs 7).toNat ≤ 2368)
    (hI : ImgOk enc base s.mem E) (hE : ∀ i, 3 ≤ i → i < 95 → ¬ E i) :
    ∃ s6, run 6 s = some s6 ∧ s6.rip = base + 36 ∧ s6.mem = s.mem ∧
      s6.regs 7 = BitVec.ofNat 64 ((s.regs 7).toNat / 8 - 1) ∧
      s6.regs 6 = BitVec.ofNat 64 (27 * ((s.regs 7).toNat / 8 - 1)) ∧
      ∀ i : Fin 16, i.val ≠ 6 → i.val ≠ 7 → s6.regs i = s.regs i := by
  have dec := intro_dec enc henc base s.mem E hI hE
  have hlt : (s.regs 7).toNat < 2 ^ 64 := (s.regs 7).isLt
  -- sub rdi, 2368
  have d1 : decode s.mem s.rip = some (.aluRI 5 7 2368, 7) := by
    rw [hrip]; exact dec (.aluRI 5 7 2368, 9, 7) (by decide)
  obtain ⟨a1, b1, c1, e1, f1⟩ := exec_aluRI_facts 5 7 2368 7 s (by decide)
  have st1 := step_of_decode s _ _ d1
  generalize exec (.aluRI 5 7 2368) 7 s = s1 at a1 b1 c1 e1 f1 st1
  rw [sext2368, aluW_sub_cmp] at c1 e1
  -- jg (not taken)
  have hnot : cond 15 s1.fl = false := by
    cases hc : cond 15 s1.fl
    · rfl
    · exfalso
      rw [c1] at hc
      have := (jg_after_cmp (s.regs 7) 2368 s.fl.cf (by omega) (by decide)).1.1 hc
      rw [toNat2368] at this
      omega
  have d2 : decode s1.mem s1.rip = some (.jcc 15 0x4C, 2) := by
    rw [b1, a1, hrip]; exact dec (.jcc 15 0x4C, 16, 2) (by decide)
  obtain ⟨a2, b2, c2, d2', e2⟩ := exec_jcc_facts 15 0x4C 2 s1
  have st2 := step_of_decode s1 _ _ d2
  have r2 : (exec (.jcc 15 0x4C) 2 s1).rip = base + 18 := by rw [e2 hnot, a1, hrip]
  generalize exec (.jcc 15 0x4C) 2 s1 = s2 at a2 b2 c2 d2' e2 r2 st2
  have m2 : s2.mem = s.mem := by rw [b2, b1]
  have g2 : s2.regs = s1.regs := a2
  -- add rdi, 2368
  have d3 : decode s2.mem s2.rip = some (.aluRI 0 7 2368, 7) := by
    rw [m2, r2]; exact dec (.aluRI 0 7 2368, 18, 7) (by decide)
  obtain ⟨s3, st3, r3, m3, v3, g3⟩ := regstep_run s2 _ _ _ _ rs_addrdi d3
  -- shr rdi, 3
  have d4 : decode s3.mem s3.rip = some (.shiftI 5 7 3, 4) := by
    rw [m3, r3, m2, r2]; exact dec (.shiftI 5 7 3, 25, 4) (by decide)
  obtain ⟨s4, st4, r4, m4, v4, g4⟩ := regstep_run s3 _ _ _ _ rs_shr d4
  -- dec rdi
  have d5 : decode s4.mem s4.rip = some (.dec 7, 3) := by
    rw [m4, m3, m2, r4, r3, r2]; exact dec (.dec 7, 29, 3) (by decide)
  obtain ⟨s5, st5, r5, m5, v5, g5⟩ := regstep_run s4 _ _ _ _ rs_dec d5
  -- imul rsi, rdi, 27
  have d6 : decode s5.mem s5.rip = some (.imulI 6 7 27, 4) := by
    rw [m5, m4, m3, m2, r5, r4, r3, r2]; exact dec (.imulI 6 7 27, 32, 4) (by decide)
  obtain ⟨s6, st6, r6, m6, v6, g6⟩ := regstep_run s5 _ _ _ _ rs_imul d6
  -- values
  have hR : s3.regs 7 = s.regs 7 := by
    rw [v3, g2, e1]
    show (s.regs 7 - 2368) + 2368 = _
    exact BitVec.sub_add_cancel _ _
  have hdec : s5.regs 7 = BitVec.ofNat 64 ((s.regs 7).toNat / 8 - 1) := by
    rw [v5, v4, hR]; exact shr_dec _ hR1
  have hdl : (s.regs 7).toNat / 8 - 1 < 296 := by omega
  have hsix : s6.regs 6 = BitVec.ofNat 64 (27 * ((s.regs 7).toNat / 8 - 1)) := by
    rw [v6, hdec]
    exact imul27 _ hdl
  refine ⟨s6, ?_, ?_, ?_, ?_, hsix, ?_⟩
  · rw [run_succ_some 5 s s1 st1, run_succ_some 4 s1 s2 st2, run_succ_some 3 s2 s3 st3, run_succ_some 2 s3 s4 st4,
      run_succ_some 1 s4 s5 st5, run_succ_some 0 s5 s6 st6]; rfl
  · rw [r6, r5, r4, r3, r2]
  · rw [m6, m5, m4, m3, m2]
  · rw [g6 7 (by decide), hdec]
  · intro i h6 h7
    have i6 : i ≠ 6 := fun e => h6 (by rw [e]; rfl)
    have i7 : i ≠ 7 := fun e => h7 (by rw [e]; rfl)
    rw [g6 i i6, g5 i i7, g4 i i7, g3 i i7, g2, f1 i i7]


theorem rsiOf_eq (w : Nat) : rsiOf w = 27 * w + (if 148 ≤ w then 5 else 0) := by
  simp [rsiOf, unitLen, perPage_148, nopPad_5]

theorem toNat_ofNat64_148 : (148 : BitVec 64).toNat = 148 := by decide

/-- `cmp rdi, 148; jl` after `rdi = w`. -/
theorem cmp_jl (enc : Instr → List Nat) (henc : EncOk enc) (base : Nat) (s : St) (E : Nat → Prop) (w : Nat) (hw : w < 296)
    (hrip : s.rip = base + 36) (h7 : s.regs 7 = BitVec.ofNat 64 w) (hI : ImgOk enc base s.mem E)
    (hE : ∀ i, 3 ≤ i → i < 95 → ¬ E i) :
    ∃ s2, run 2 s = some s2 ∧ s2.mem = s.mem ∧ s2.regs = s.regs ∧
      (w < 148 → s2.rip = base + 48) ∧ (148 ≤ w → s2.rip = base + 45) := by
  have dec := intro_dec enc henc base s.mem E hI hE
  have d1 : decode s.mem s.rip = some (.aluRI 7 7 148, 7) := by
    rw [hrip]; exact dec (.aluRI 7 7 148, 36, 7) (by decide)
  obtain ⟨a1, b1, c1, e1⟩ := exec_cmpRI_facts 7 148 7 s
  have st1 := step_of_decode s _ _ d1
  generalize exec (.aluRI 7 7 148) 7 s = s1 at a1 b1 c1 e1 st1
  rw [sext148, h7] at e1
  have d2 : decode s1.mem s1.rip = some (.jcc 12 3, 2) := by
    rw [b1, a1, hrip]; exact dec (.jcc 12 3, 43, 2) (by decide)
  obtain ⟨a2, b2, c2, d2', e2⟩ := exec_jcc_facts 12 3 2 s1
  have st2 := step_of_decode s1 _ _ d2
  have hw1 : (BitVec.ofNat 64 w).toNat < 2 ^ 63 := by rw [toNat_ofNat64_small w (by omega)]; omega
  have hjl := jl_after_cmp (BitVec.ofNat 64 w) 148 s.fl.cf hw1 (by decide)
  rw [toNat_ofNat64_small w (by omega), toNat_ofNat64_148] at hjl
  generalize exec (.jcc 12 3) 2 s1 = s2 at a2 b2 c2 d2' e2 st2
  have h3 : (3 : BitVec 8).toInt = 3 := by decide
  refine ⟨s2, run_two s s1 s2 st1 st2, by rw [b2, b1], by rw [a2]; exact c1, ?_, ?_⟩
  · intro h
    have hc : cond 12 s1.fl = true := by rw [e1]; exact hjl.2 h
    rw [d2' hc, a1, hrip, h3]; simp only [Int.ofNat_eq_natCast]; omega
  · intro h
    have hc : cond 12 s1.fl = false := by
      cases hh : cond 12 s1.fl
      · rfl
      · exfalso; have := hjl.1 (by rw [← e1]; exact hh); omega
    rw [e2 hc, a1, hrip]


theorem intro_mid_lt (enc : Instr → List Nat) (henc : EncOk enc) (base : Nat) (s : St) (E : Nat → Prop) (w : Nat)
    (hw : w < 148) (hrip : s.rip = base + 36) (h7 : s.regs 7 = BitVec.ofNat 64 w)
    (h6 : s.regs 6 = BitVec.ofNat 64 (27 * w)) (hI : ImgOk enc base s.mem E) (hE : ∀ i, 3 ≤ i → i < 95 → ¬ E i) :
    ∃ s', run 2 s = some s' ∧ s'.rip = base + 48 ∧ s'.mem = s.mem ∧ s'.regs = s.regs := by
  obtain ⟨s2, e2, m2, g2, r148, r45⟩ := cmp_jl enc henc base s E w (by omega) hrip h7 hI hE
  exact ⟨s2, e2, r148 hw, m2, g2⟩

theorem intro_mid_ge (enc : Instr → List Nat) (henc : EncOk enc) (base : Nat) (s : St) (E : Nat → Prop) (w : Nat)
    (hw : 148 ≤ w) (hw2 : w < 296) (hrip : s.rip = base + 36) (h7 : s.regs 7 = BitVec.ofNat 64 w)
    (h6 : s.regs 6 = BitVec.ofNat 64 (27 * w)) (hI : ImgOk enc base s.mem E) (hE : ∀ i, 3 ≤ i → i < 95 → ¬ E i) :
    ∃ s', run 3 s = some s' ∧ s'.rip = base + 48 ∧ s'.mem = s.mem ∧
      s'.regs 6 = BitVec.ofNat 64 (27 * w + 5) ∧ (∀ i : Fin 16, i.val ≠ 6 → s'.regs i = s.regs i) := by
  have dec := intro_dec enc henc base s.mem E hI hE
  obtain ⟨s2, e2, m2, g2, r148, r45⟩ := cmp_jl enc henc base s E w hw2 hrip h7 hI hE
  have r2 := r45 hw
  have d3 : decode s2.mem s2.rip = some (.aluRI8_32 0 6 5, 3) := by
    rw [m2, r2]; exact dec (.aluRI8_32 0 6 5, 45, 3) (by decide)
  obtain ⟨s3, st3, r3, m3, v3, g3⟩ := regstep_run s2 _ _ _ _ rs_add32 d3
  have hrun : run 3 s = some s3 := by
    rw [show (3 : Nat) = 2 + 1 from rfl, run_add, e2]
    simp only [Option.bind_some]
    rw [run_one, st3]
  refine ⟨s3, hrun, ?_, ?_, ?_, ?_⟩
  · rw [r3, r2]
  · rw [m3, m2]
  · rw [v3, g2, h6]; exact add32_5 _ (by omega)
  · intro i h6'
    have : i ≠ 6 := fun e => h6' (by rw [e]; rfl)
    rw [g3 i this, g2]

theorem loopAt_xorq (enc : Instr → List Nat) (h : EncOk enc) :
    loopAt enc 81 = 0x48 ∧ loopAt enc 82 = 0x31 ∧ loopAt enc 83 = 0x3D ∧
    (∀ j, j < 4 → loopAt enc (84 + j) = (bytes32 (sdisp 30)).getD j 0) := by
  rcases h with rfl | rfl <;> decide +kernel

theorem loopAt_xorq_tail (enc : Instr → List Nat) (h : EncOk enc) :
    loopAt enc 8103 = 0x48 ∧ loopAt enc 8104 = 0x31 ∧ loopAt enc 8105 = 0x3D ∧
    (∀ j, j < 4 → loopAt enc (8106 + j) = (bytes32 (sdisp ((leaOff 0 : Int) - 8110))).getD j 0) := by
  rcases h with rfl | rfl <;> decide +kernel

theorem tab_encode (enc : Instr → List Nat) (h : EncOk enc) :
    enc (.aluMR32 0 3 6) = encode (.aluMR32 0 3 6) ∧ enc (.aluMR32 5 (sdisp (-10)) 6) = encode (.aluMR32 5 (sdisp (-10)) 6) := by
  rcases h with rfl | rfl <;> exact ⟨rfl, rfl⟩


end SmcTamper
