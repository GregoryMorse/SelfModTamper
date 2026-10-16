module
public import SmcTamper.Unrolled.L2Decode
public import SmcTamper.Layout.Targets

@[expose] public section

namespace SmcTamper

set_option linter.unusedVariables false

/-! ## Level 2 of the unrolled kernel, part 2: one unit on the instruction-level machine refines `unitStep`

Seven instructions (`adc` .. `xor [rip+d], dl`) compute `unitStep`'s sum and memory; the eighth (`lea rcx,[rcx+8]`) advances the pointer. -/

theorem unitDisp_toInt (u : Nat) (hu : u < 296) :
    (unitDisp u).toInt = (opOff ((u + perPage) % numUnits) : Int) - ((unitStart u + 23 : Nat) : Int) := by
  have h1 := rsiOf_spec u
  have h2 := rsiOf_spec ((u + 148) % 296)
  have hp : perPage = 148 := perPage_148
  have hn : numUnits = 296 := numUnits_296
  unfold unitDisp
  apply toInt_sdisp <;> (simp only [opOff, unitStart, introLen, hp, hn] at *; omega)

theorem imgOk_wr8 (enc : Instr → List Nat) (base : Nat) (M : Mem) (E : Nat → Prop) (hI : ImgOk enc base M E) (t : Nat) (ht : t < 296)
    (b : BitVec 8) : ImgOk enc base (wr8 M (base + opOff t) b) E := by
  intro i hi hop hE
  have := hI i hi hop hE
  have hne : i ≠ opOff t := hop t ht
  rw [← this]
  simp [wr8, hne]

theorem kernelOps_wr8 (base : Nat) (M : Mem) (hK : ∀ v, v < 296 → IsKernelOpcode (M (base + opOff v))) (t : Nat) (ht : t < 296)
    (res : BitVec 64) :
    ∀ v, v < 296 → IsKernelOpcode (wr8 M (base + opOff t) (M (base + opOff t) ^^^ (BitVec.ofNat 8 (toggle res) <<< 3)) (base + opOff v)) := by
  intro v hv
  by_cases e : v = t
  · subst e
    simp only [wr8, if_true]
    exact kernelOpcode_xor_closed _ (hK v hv) res
  · have : base + opOff v ≠ base + opOff t := by
      intro h; apply e; exact opOff_inj _ _ hv ht (by omega)
    simp only [wr8, this, if_false]
    exact hK v hv

theorem unit7 (enc : Instr → List Nat) (henc : EncOk enc) (base : Nat) (E : Nat → Prop) (s : St) (u : Nat) (hu : u < 296)
    (hrip : s.rip = base + unitStart u) (hcf : s.fl.cf = false) (hI : ImgOk enc base s.mem E)
    (hE : ∀ o, o < 23 → ¬ E (unitStart u + o)) (hK : ∀ v, v < 296 → IsKernelOpcode (s.mem (base + opOff v))) :
    ∃ s7, run 7 s = some s7 ∧ s7.rip = base + unitStart u + 23 ∧ s7.fl.cf = false ∧
      s7.regs 3 = (unitStep base u ⟨s.mem, (s.regs 1).toNat, s.regs 3⟩).sum ∧
      s7.mem = (unitStep base u ⟨s.mem, (s.regs 1).toNat, s.regs 3⟩).mem ∧
      (∀ i : Fin 16, i.val ≠ 0 → i.val ≠ 2 → i.val ≠ 3 → s7.regs i = s.regs i) := by
  have hop1 : IsKernelOpcode (s.mem (base + unitStart u + 1)) := by
    have := hK u hu; simpa [opOff, Nat.add_assoc] using this
  obtain ⟨F, hF⟩ : ∃ F : Fin 8, F = Fin.ofNat 8 (aluField (s.mem (base + unitStart u + 1))) := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : BitVec 64 × Flags, P = aluW F (s.regs 3) (rd64 s.mem (s.regs 1).toNat) false := ⟨_, rfl⟩
  -- 1: ADC/SBB/XOR/CMP RBX,[RCX]
  obtain ⟨s1, e1, r1, m1, f1, g1, h1⟩ : ∃ s1, step s = some s1 ∧ s1.rip = base + unitStart u + 3 ∧ s1.mem = s.mem ∧
      s1.fl = P.2 ∧ s1.regs 3 = (if F = 7 then s.regs 3 else P.1) ∧ (∀ i, i ≠ 3 → s1.regs i = s.regs i) := by
    have d : decode s.mem s.rip = some (.aluM F 3 1, 3) := by
      rw [hrip, hF]; exact du_aluM enc henc base s.mem E hI u hu (fun o ho => hE o ho) hop1
    obtain ⟨a, b, c, e, f⟩ := exec_aluM_facts F 3 1 3 s
    refine ⟨_, step_of_decode s _ _ d, ?_, b, ?_, ?_, e⟩
    · rw [a, hrip]
    · rw [c, hcf, hP]
    · rw [f, hcf, hP]
  have hPsf : P.2.sf = sf P.1 := by rw [hP]; exact (aluW_pf_sf F _ _ false).2
  have hPpf : P.2.pf = pf P.1 := by rw [hP]; exact (aluW_pf_sf F _ _ false).1
  have c2 : (2 : BitVec 8).toNat % 32 = 2 := by decide
  have c3 : (3 : BitVec 8).toNat % 32 = 3 := by decide
  -- 2: SETS DL
  obtain ⟨s2, e2, r2, m2, f2, g2, l2, k2⟩ : ∃ s2, step s1 = some s2 ∧ s2.rip = base + unitStart u + 6 ∧ s2.mem = s.mem ∧
      s2.fl = P.2 ∧ (∀ i : Fin 16, i.val ≠ 2 → s2.regs i = s1.regs i) ∧
      s2.low8 2 = (if sf P.1 then 1 else 0) ∧ s2.low8 0 = s1.low8 0 := by
    have d : decode s1.mem s1.rip = some (.setcc 8 2, 3) := by
      rw [m1, r1]
      exact du_const enc henc base s.mem E hI u hu (.setcc 8 2) (by simp [constInstrs]) 3 3
        (by rcases henc with rfl | rfl <;> rfl) (by omega) (by omega) (by omega)
        (fun k hk => by rw [show unitStart u + 3 + k = unitStart u + (3 + k) by omega]; exact hE _ (by omega))
        (by rcases henc with rfl | rfl <;> rfl)
    obtain ⟨a, b, c, e, f, g⟩ := exec_setcc_facts 8 2 3 s1
    refine ⟨_, step_of_decode s1 _ _ d, ?_, ?_, ?_, e, ?_, g 0 (by decide)⟩
    · rw [a, r1]
    · rw [b, m1]
    · rw [c, f1]
    · rw [f, cond_S, f1, hPsf]
  -- 3: SETP AL
  obtain ⟨s3, e3, r3, m3, f3, g3, l3, k3⟩ : ∃ s3, step s2 = some s3 ∧ s3.rip = base + unitStart u + 9 ∧ s3.mem = s.mem ∧
      s3.fl = P.2 ∧ (∀ i : Fin 16, i.val ≠ 0 → s3.regs i = s2.regs i) ∧
      s3.low8 0 = (if pf P.1 then 1 else 0) ∧ s3.low8 2 = s2.low8 2 := by
    have d : decode s2.mem s2.rip = some (.setcc 10 0, 3) := by
      rw [m2, r2]
      exact du_const enc henc base s.mem E hI u hu (.setcc 10 0) (by simp [constInstrs]) 6 3
        (by rcases henc with rfl | rfl <;> rfl) (by omega) (by omega) (by omega)
        (fun k hk => by rw [show unitStart u + 6 + k = unitStart u + (6 + k) by omega]; exact hE _ (by omega))
        (by rcases henc with rfl | rfl <;> rfl)
    obtain ⟨a, b, c, e, f, g⟩ := exec_setcc_facts 10 0 3 s2
    refine ⟨_, step_of_decode s2 _ _ d, ?_, ?_, ?_, e, ?_, g 2 (by decide)⟩
    · rw [a, r2]
    · rw [b, m2]
    · rw [c, f2]
    · rw [f, cond_P, f2, hPpf]
  -- 4: SHL AL,2
  obtain ⟨s4, e4, r4, m4, g4, l4, k4⟩ : ∃ s4, step s3 = some s4 ∧ s4.rip = base + unitStart u + 12 ∧ s4.mem = s.mem ∧
      (∀ i : Fin 16, i.val ≠ 0 → s4.regs i = s3.regs i) ∧
      s4.low8 0 = s3.low8 0 <<< 2 ∧ s4.low8 2 = s3.low8 2 := by
    have d : decode s3.mem s3.rip = some (.shlB 0 2, 3) := by
      rw [m3, r3]
      exact du_const enc henc base s.mem E hI u hu (.shlB 0 2) (by simp [constInstrs]) 9 3
        (by rcases henc with rfl | rfl <;> rfl) (by omega) (by omega) (by omega)
        (fun k hk => by rw [show unitStart u + 9 + k = unitStart u + (9 + k) by omega]; exact hE _ (by omega))
        (by rcases henc with rfl | rfl <;> rfl)
    obtain ⟨a, b, c, e, f⟩ := exec_shlB_facts 0 2 (by decide) 3 s3
    refine ⟨_, step_of_decode s3 _ _ d, ?_, ?_, c, ?_, f 2 (by decide)⟩
    · rw [a, r3]
    · rw [b, m3]
    · rw [e, c2]
  -- 5: OR DL,AL
  obtain ⟨s5, e5, r5, m5, g5, l5⟩ : ∃ s5, step s4 = some s5 ∧ s5.rip = base + unitStart u + 14 ∧ s5.mem = s.mem ∧
      (∀ i : Fin 16, i.val ≠ 2 → s5.regs i = s4.regs i) ∧ s5.low8 2 = s4.low8 2 ||| s4.low8 0 := by
    have d : decode s4.mem s4.rip = some (.orB 2 0, 2) := by
      rw [show s4.mem = s.mem from m4, r4]
      exact du_const enc henc base s.mem E hI u hu (.orB 2 0) (by simp [constInstrs]) 12 2
        (by rcases henc with rfl | rfl <;> rfl) (by omega) (by omega) (by omega)
        (fun k hk => by rw [show unitStart u + 12 + k = unitStart u + (12 + k) by omega]; exact hE _ (by omega))
        (by rcases henc with rfl | rfl <;> rfl)
    obtain ⟨a, b, c, e, f⟩ := exec_orB_facts 2 0 (by decide) 2 s4
    refine ⟨_, step_of_decode s4 _ _ d, ?_, ?_, c, e⟩
    · rw [a, r4]
    · rw [b, m4]
  -- 6: SHL DL,3
  obtain ⟨s6, e6, r6, m6, g6, l6⟩ : ∃ s6, step s5 = some s6 ∧ s6.rip = base + unitStart u + 17 ∧ s6.mem = s.mem ∧
      (∀ i : Fin 16, i.val ≠ 2 → s6.regs i = s5.regs i) ∧ s6.low8 2 = s5.low8 2 <<< 3 := by
    have d : decode s5.mem s5.rip = some (.shlB 2 3, 3) := by
      rw [m5, r5]
      exact du_const enc henc base s.mem E hI u hu (.shlB 2 3) (by simp [constInstrs]) 14 3
        (by rcases henc with rfl | rfl <;> rfl) (by omega) (by omega) (by omega)
        (fun k hk => by rw [show unitStart u + 14 + k = unitStart u + (14 + k) by omega]; exact hE _ (by omega))
        (by rcases henc with rfl | rfl <;> rfl)
    obtain ⟨a, b, c, e, f⟩ := exec_shlB_facts 2 3 (by decide) 3 s5
    refine ⟨_, step_of_decode s5 _ _ d, ?_, ?_, c, ?_⟩
    · rw [a, r5]
    · rw [b, m5]
    · rw [e, c3]
  have hdl : s6.low8 2 = BitVec.ofNat 8 (toggle P.1) <<< 3 := by
    rw [l6, l5, k4, l4, l3, k3, l2]
    rw [← toggle_byte P.1]
  -- 7: XOR [opcode byte of unit (u+148) mod 296],DL
  obtain ⟨t, ht⟩ : ∃ t, t = (u + 148) % 296 := ⟨_, rfl⟩
  have htl : t < 296 := by omega
  have hea : ripEA s6.rip 6 (unitDisp u) = base + opOff t := by
    have hd := unitDisp_toInt u hu
    have hp : perPage = 148 := perPage_148
    have hn : numUnits = 296 := numUnits_296
    rw [hp, hn, ← ht] at hd
    unfold ripEA
    rw [r6, hd, Int.ofNat_eq_natCast]
    simp only [opOff, unitStart] at *
    omega
  obtain ⟨s7, e7, r7, m7, g7, c7⟩ : ∃ s7, step s6 = some s7 ∧ s7.rip = base + unitStart u + 23 ∧
      s7.mem = wr8 s.mem (base + opOff t) (s.mem (base + opOff t) ^^^ (BitVec.ofNat 8 (toggle P.1) <<< 3)) ∧
      (∀ i, s7.regs i = s6.regs i) ∧ s7.fl.cf = false := by
    have d : decode s6.mem s6.rip = some (.xorMB (unitDisp u) 2, 6) := by
      rw [m6, r6]
      exact du_xor enc henc base s.mem E hI u hu
        (fun k hk => by rw [show unitStart u + 17 + k = unitStart u + (17 + k) by omega]; exact hE _ (by omega))
    refine ⟨_, step_of_decode s6 _ _ d, ?_, ?_, fun i => rfl, rfl⟩
    · show s6.rip + 6 = _
      rw [r6] <;> omega
    · show wr8 s6.mem (ripEA s6.rip 6 (unitDisp u)) _ = _
      rw [hea, m6, hdl]
  have hrun : run 7 s = some s7 := by
    rw [run_succ_some 6 s s1 e1, run_succ_some 5 s1 s2 e2, run_succ_some 4 s2 s3 e3, run_succ_some 3 s3 s4 e4,
      run_succ_some 2 s4 s5 e5, run_succ_some 1 s5 s6 e6, run_succ_some 0 s6 s7 e7]
    rfl
  have hF7 : (F = 7) ↔ aluField (s.mem (base + unitStart u + 1)) = 7 := by rw [hF]; exact fin8_ofNat_eq7 _
  have hread : s.mem (base + opOff u) = s.mem (base + unitStart u + 1) := by simp [opOff, Nat.add_assoc]
  have hmem7 : s7.mem = (unitStep base u ⟨s.mem, (s.regs 1).toNat, s.regs 3⟩).mem := by
    rw [m7]
    unfold unitStep kAlu
    dsimp only
    rw [hread, ← hF, ← hP, ht]
    simp only [perPage, numUnits]
    rfl
  refine ⟨s7, hrun, r7, ?_, ?_, hmem7, ?_⟩
  · exact c7
  · have r3' : s7.regs 3 = s1.regs 3 := by
      rw [g7, g6 3 (by decide), g5 3 (by decide), g4 3 (by decide), g3 3 (by decide), g2 3 (by decide)]
    rw [r3', g1]
    unfold unitStep kAlu
    dsimp only
    simp only [hread]
    by_cases hh : F = 7
    · rw [if_pos hh, if_pos (hF7.1 hh)]
    · rw [if_neg hh, if_neg (mt hF7.2 hh), hP, hF]
  · intro i h0 h2 h3
    have hi3 : i ≠ 3 := fun e => h3 (by rw [e]; rfl)
    rw [g7, g6 i h2, g5 i h2, g4 i h0, g3 i h0, g2 i h2, h1 i hi3]

/-- The eighth instruction of a unit: `lea rcx,[rcx+8]`. -/
theorem unit_lea (enc : Instr → List Nat) (henc : EncOk enc) (base : Nat) (E : Nat → Prop) (s : St) (u : Nat) (hu : u < 296)
    (hrip : s.rip = base + unitStart u + 23) (hI : ImgOk enc base s.mem E)
    (hE : ∀ o, 23 ≤ o → o < 27 → ¬ E (unitStart u + o)) :
    ∃ s8, step s = some s8 ∧ s8.rip = base + unitStart u + 27 ∧ s8.mem = s.mem ∧ s8.fl = s.fl ∧
      s8.regs 1 = s.regs 1 + 8 ∧ (∀ i, i ≠ 1 → s8.regs i = s.regs i) := by
  have d : decode s.mem s.rip = some (.leaD 1 1 8, 4) := by
    rw [hrip]
    exact du_const enc henc base s.mem E hI u hu (.leaD 1 1 8) (by simp [constInstrs]) 23 4
      (by rcases henc with rfl | rfl <;> rfl) (by omega) (by omega) (by omega)
      (fun k hk => by rw [show unitStart u + 23 + k = unitStart u + (23 + k) by omega]; exact hE _ (by omega) (by omega))
      (by rcases henc with rfl | rfl <;> rfl)
  have sx : (8 : BitVec 8).signExtend 64 = 8 := by decide
  refine ⟨_, step_of_decode s _ _ d, ?_, rfl, rfl, ?_, ?_⟩
  · show s.rip + 4 = _
    rw [hrip] <;> omega
  · rw [exec_leaD, sx]; simp [St.setReg]
  · intro i hi; rw [exec_leaD]; simp [St.setReg, hi]

end SmcTamper
