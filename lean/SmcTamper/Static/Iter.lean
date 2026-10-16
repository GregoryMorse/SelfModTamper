module
public import SmcTamper.Static.Emulation
public import SmcTamper.X64.Run

@[expose] public section

namespace SmcTamper

theorem run_succ_some (n : Nat) (s s' : St) (h : step s = some s') : run (n + 1) s = run n s' := by
  simp [run, h]

theorem aluW_pf_sf {w : Nat} (f : Fin 8) (a b : BitVec w) (c : Bool) :
    (aluW f a b c).2.pf = pf (aluW f a b c).1 ∧ (aluW f a b c).2.sf = sf (aluW f a b c).1 := by
  unfold aluW
  generalize f.val = v
  rcases v with _ | _ | _ | _ | _ | _ | _ | _ | v <;> simp [logicFlags]

theorem fin8_ofNat_eq7 (b : BitVec 8) : (Fin.ofNat 8 (aluField b) = (7 : Fin 8)) ↔ aluField b = 7 := by
  have : aluField b < 8 := by unfold aluField; omega
  rw [Fin.ext_iff]
  simp [Fin.val_ofNat]
  omega

theorem low8_setLow8_self (s : St) (r : Fin 4) (v : BitVec 8) : (s.setLow8 r v).low8 r = v := by
  unfold St.setLow8 St.low8 St.setReg
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi]

theorem low8_setLow8_other (s : St) (r r' : Fin 4) (v : BitVec 8) (h : r ≠ r') :
    (s.setLow8 r v).low8 r' = s.low8 r' := by
  have : (⟨r'.val, by omega⟩ : Fin 16) ≠ ⟨r.val, by omega⟩ := by
    intro e; apply h; apply Fin.ext; have := congrArg Fin.val e; simpa using this.symm
  unfold St.setLow8 St.low8 St.setReg
  simp [this]

theorem regs_setLow8 (s : St) (r : Fin 4) (v : BitVec 8) (i : Fin 16) (h : i.val ≠ r.val) :
    (s.setLow8 r v).regs i = s.regs i := by
  unfold St.setLow8 St.setReg
  have : i ≠ ⟨r.val, by omega⟩ := by intro e; apply h; simp [e]
  simp [this]

theorem toggle_byte (res : BitVec 64) :
    ((if sf res then (1 : BitVec 8) else 0) ||| ((if pf res then (1 : BitVec 8) else 0) <<< 2)) <<< 3
      = BitVec.ofNat 8 (toggle res) <<< 3 := by
  unfold toggle
  cases pf res <;> cases sf res <;> decide

/-- The addresses of the instructions executed in the first `n` steps (the control-flow trace). -/
def trace : Nat → St → List Nat
  | 0, _ => []
  | n + 1, s => s.rip :: (match step s with | some s' => trace n s' | none => [])

theorem trace_succ_some (n : Nat) (s s' : St) (h : step s = some s') : trace (n + 1) s = s.rip :: trace n s' := by
  simp [trace, h]

theorem trace_add (a b : Nat) : ∀ (s s'' : St), run a s = some s'' → trace (a + b) s = trace a s ++ trace b s'' := by
  induction a with
  | zero => intro s s'' h; simp [run] at h; subst h; simp [trace]
  | succ a ih =>
    intro s s'' h
    cases hst : step s with
    | none => simp [run, hst] at h
    | some s1 =>
      simp [run, hst] at h
      have : a + 1 + b = (a + b) + 1 := by omega
      rw [this, trace_succ_some _ s s1 hst, trace_succ_some _ s s1 hst, ih s1 s'' h]
      simp

/-- The instruction addresses of one loop iteration (offsets from `MOV RSI,RCX`). -/
def iterRips (a0 : Nat) : List Nat :=
  [a0 + 11, a0 + 14, a0 + 17, a0 + 20, a0 + 23, a0 + 25, a0 + 28, a0 + 34, a0 + 38, a0 + 41]

theorem exec_aluM_facts (f : Fin 8) (d b : Fin 16) (len : Nat) (s : St) :
    (exec (.aluM f d b) len s).rip = s.rip + len ∧ (exec (.aluM f d b) len s).mem = s.mem ∧
    (exec (.aluM f d b) len s).fl = (aluW f (s.regs d) (rd64 s.mem (s.regs b).toNat) s.fl.cf).2 ∧
    (∀ i, i ≠ d → (exec (.aluM f d b) len s).regs i = s.regs i) ∧
    (exec (.aluM f d b) len s).regs d =
      (if f = 7 then s.regs d else (aluW f (s.regs d) (rd64 s.mem (s.regs b).toNat) s.fl.cf).1) := by
  unfold exec
  by_cases h : f = 7
  · simp [h]
  · simp [h, St.setReg]
    intro i hi; simp [hi]

theorem fin16_ne (a b : Fin 16) (h : a.val ≠ b.val) : a ≠ b := fun e => h (by rw [e])

theorem low8_fl (s : St) (r : Fin 4) (f : Flags) : ({ s with fl := f } : St).low8 r = s.low8 r := rfl

theorem exec_setcc_facts (cc : Fin 16) (r : Fin 4) (len : Nat) (s : St) :
    (exec (.setcc cc r) len s).rip = s.rip + len ∧ (exec (.setcc cc r) len s).mem = s.mem ∧
    (exec (.setcc cc r) len s).fl = s.fl ∧
    (∀ i : Fin 16, i.val ≠ r.val → (exec (.setcc cc r) len s).regs i = s.regs i) ∧
    (exec (.setcc cc r) len s).low8 r = (if cond cc s.fl then 1 else 0) ∧
    (∀ r' : Fin 4, r ≠ r' → (exec (.setcc cc r) len s).low8 r' = s.low8 r') := by
  rw [exec_setcc]
  refine ⟨rfl, rfl, rfl, fun i hi => regs_setLow8 _ _ _ _ hi, low8_setLow8_self _ _ _, fun r' h => ?_⟩
  exact low8_setLow8_other _ _ _ _ h

theorem exec_shlB_facts (r : Fin 4) (n : BitVec 8) (hn : n.toNat % 32 ≠ 0) (len : Nat) (s : St) :
    (exec (.shlB r n) len s).rip = s.rip + len ∧ (exec (.shlB r n) len s).mem = s.mem ∧
    (∀ i : Fin 16, i.val ≠ r.val → (exec (.shlB r n) len s).regs i = s.regs i) ∧
    (exec (.shlB r n) len s).low8 r = s.low8 r <<< (n.toNat % 32) ∧
    (∀ r' : Fin 4, r ≠ r' → (exec (.shlB r n) len s).low8 r' = s.low8 r') := by
  have e : exec (.shlB r n) len s = { ({ s with rip := s.rip + len } : St).setLow8 r (s.low8 r <<< (n.toNat % 32)) with
      fl := (shiftW true (s.low8 r) (n.toNat % 32) s.fl).2 } := by
    simp [exec, shiftW, hn]
  rw [e]
  refine ⟨rfl, rfl, fun i hi => regs_setLow8 _ _ _ _ hi, low8_setLow8_self _ _ _, fun r' h => ?_⟩
  exact low8_setLow8_other _ _ _ _ h

theorem exec_orB_facts (d r : Fin 4) (hdr : d ≠ r) (len : Nat) (s : St) :
    (exec (.orB d r) len s).rip = s.rip + len ∧ (exec (.orB d r) len s).mem = s.mem ∧
    (∀ i : Fin 16, i.val ≠ d.val → (exec (.orB d r) len s).regs i = s.regs i) ∧
    (exec (.orB d r) len s).low8 d = s.low8 d ||| s.low8 r ∧
    (∀ r' : Fin 4, d ≠ r' → (exec (.orB d r) len s).low8 r' = s.low8 r') := by
  have e : exec (.orB d r) len s = { ({ s with rip := s.rip + len } : St).setLow8 d (s.low8 d ||| s.low8 r) with
      fl := logicFlags (s.low8 d ||| s.low8 r) } := rfl
  rw [e]
  refine ⟨rfl, rfl, fun i hi => regs_setLow8 _ _ _ _ hi, low8_setLow8_self _ _ _, fun r' h => ?_⟩
  exact low8_setLow8_other _ _ _ _ h

theorem exec_jcc_facts (cc : Fin 16) (rel : BitVec 8) (len : Nat) (s : St) :
    (exec (.jcc cc rel) len s).regs = s.regs ∧ (exec (.jcc cc rel) len s).mem = s.mem ∧
    (exec (.jcc cc rel) len s).fl = s.fl ∧
    (cond cc s.fl = true → (exec (.jcc cc rel) len s).rip = (Int.ofNat (s.rip + len) + rel.toInt).toNat) ∧
    (cond cc s.fl = false → (exec (.jcc cc rel) len s).rip = s.rip + len) := by
  unfold exec
  by_cases h : cond cc s.fl = true <;> simp [h]

theorem iter_run (a0 : Nat) (s : St) (hrip : s.rip = a0 + 11) (hcode : CodeOk s.mem a0)
    (hkop : IsKernelOpcode (s.mem (a0 + 12))) (hcf : s.fl.cf = false)
    (hp : (s.regs 6).toNat + 8 < 2 ^ 63) (he : (s.regs 7).toNat < 2 ^ 63) :
    ∃ s', run 10 s = some s' ∧
      s'.regs 3 = (staticStep (a0 + 12) ⟨s.mem, (s.regs 6).toNat, s.regs 3⟩).sum ∧
      s'.mem = (staticStep (a0 + 12) ⟨s.mem, (s.regs 6).toNat, s.regs 3⟩).mem ∧
      s'.regs 6 = s.regs 6 + 8 ∧ s'.regs 7 = s.regs 7 ∧ s'.regs 8 = s.regs 8 ∧
      ((s'.regs 6).toNat < (s'.regs 7).toNat → s'.rip = a0 + 11 ∧ s'.fl.cf = false) ∧
      (¬ (s'.regs 6).toNat < (s'.regs 7).toNat → s'.rip = a0 + 43) ∧ trace 10 s = iterRips a0 := by
  -- the ALU result and its flags
  obtain ⟨F, hF⟩ : ∃ F : Fin 8, F = Fin.ofNat 8 (aluField (s.mem (a0 + 12))) := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : BitVec 64 × Flags, P = aluW F (s.regs 3) (rd64 s.mem (s.regs 6).toNat) false := ⟨_, rfl⟩
  have hcode' : CodeOk s.mem a0 := hcode
  -- 1: ADC/SBB/XOR/CMP RBX,[RSI]
  obtain ⟨s1, e1, r1, m1, f1, g1, h1⟩ : ∃ s1, step s = some s1 ∧ s1.rip = a0 + 14 ∧ s1.mem = s.mem ∧ s1.fl = P.2 ∧
      s1.regs 3 = (if F = 7 then s.regs 3 else P.1) ∧ (∀ i, i ≠ 3 → s1.regs i = s.regs i) := by
    have d : decode s.mem s.rip = some (.aluM F 3 6, 3) := by
      rw [hrip, hF]; exact dec_alu s.mem a0 hcode hkop
    obtain ⟨a, b, c, e, f⟩ := exec_aluM_facts F 3 6 3 s
    refine ⟨_, step_of_decode s _ _ d, ?_, b, ?_, ?_, e⟩
    · rw [a, hrip]
    · rw [c, hcf, hP]
    · rw [f, hcf, hP]
  have hPsf : P.2.sf = sf P.1 := by rw [hP]; exact (aluW_pf_sf F _ _ false).2
  have hPpf : P.2.pf = pf P.1 := by rw [hP]; exact (aluW_pf_sf F _ _ false).1
  have c2 : (2 : BitVec 8).toNat % 32 = 2 := by decide
  have c3 : (3 : BitVec 8).toNat % 32 = 3 := by decide
  -- 2: SETS DL
  obtain ⟨s2, e2, r2, m2, f2, g2, l2, k2⟩ : ∃ s2, step s1 = some s2 ∧ s2.rip = a0 + 17 ∧ s2.mem = s.mem ∧
      s2.fl = P.2 ∧ (∀ i : Fin 16, i.val ≠ 2 → s2.regs i = s1.regs i) ∧
      s2.low8 2 = (if sf P.1 then 1 else 0) ∧ s2.low8 0 = s1.low8 0 := by
    have d : decode s1.mem s1.rip = some (.setcc 8 2, 3) := by
      rw [m1, r1]; exact dec_sets s.mem a0 hcode
    obtain ⟨a, b, c, e, f, g⟩ := exec_setcc_facts 8 2 3 s1
    refine ⟨_, step_of_decode s1 _ _ d, ?_, ?_, ?_, e, ?_, g 0 (by decide)⟩
    · rw [a, r1]
    · rw [b, m1]
    · rw [c, f1]
    · rw [f, cond_S, f1, hPsf]
  -- 3: SETP AL
  obtain ⟨s3, e3, r3, m3, f3, g3, l3, k3⟩ : ∃ s3, step s2 = some s3 ∧ s3.rip = a0 + 20 ∧ s3.mem = s.mem ∧
      s3.fl = P.2 ∧ (∀ i : Fin 16, i.val ≠ 0 → s3.regs i = s2.regs i) ∧
      s3.low8 0 = (if pf P.1 then 1 else 0) ∧ s3.low8 2 = s2.low8 2 := by
    have d : decode s2.mem s2.rip = some (.setcc 10 0, 3) := by
      rw [m2, r2]; exact dec_setp s.mem a0 hcode
    obtain ⟨a, b, c, e, f, g⟩ := exec_setcc_facts 10 0 3 s2
    refine ⟨_, step_of_decode s2 _ _ d, ?_, ?_, ?_, e, ?_, g 2 (by decide)⟩
    · rw [a, r2]
    · rw [b, m2]
    · rw [c, f2]
    · rw [f, cond_P, f2, hPpf]
  -- 4: SHL AL,2
  obtain ⟨s4, e4, r4, m4, g4, l4, k4⟩ : ∃ s4, step s3 = some s4 ∧ s4.rip = a0 + 23 ∧ s4.mem = s.mem ∧
      (∀ i : Fin 16, i.val ≠ 0 → s4.regs i = s3.regs i) ∧
      s4.low8 0 = s3.low8 0 <<< 2 ∧ s4.low8 2 = s3.low8 2 := by
    have d : decode s3.mem s3.rip = some (.shlB 0 2, 3) := by
      rw [m3, r3]; exact dec_shlAl s.mem a0 hcode
    obtain ⟨a, b, c, e, f⟩ := exec_shlB_facts 0 2 (by decide) 3 s3
    refine ⟨_, step_of_decode s3 _ _ d, ?_, ?_, c, ?_, f 2 (by decide)⟩
    · rw [a, r3]
    · rw [b, m3]
    · rw [e, c2]
  -- 5: OR DL,AL
  obtain ⟨s5, e5, r5, m5, g5, l5⟩ : ∃ s5, step s4 = some s5 ∧ s5.rip = a0 + 25 ∧ s5.mem = s.mem ∧
      (∀ i : Fin 16, i.val ≠ 2 → s5.regs i = s4.regs i) ∧ s5.low8 2 = s4.low8 2 ||| s4.low8 0 := by
    have d : decode s4.mem s4.rip = some (.orB 2 0, 2) := by
      rw [show s4.mem = s.mem from m4, r4]; exact dec_orDlAl s.mem a0 hcode
    obtain ⟨a, b, c, e, f⟩ := exec_orB_facts 2 0 (by decide) 2 s4
    refine ⟨_, step_of_decode s4 _ _ d, ?_, ?_, c, e⟩
    · rw [a, r4]
    · rw [b, m4]
  -- 6: SHL DL,3
  obtain ⟨s6, e6, r6, m6, g6, l6⟩ : ∃ s6, step s5 = some s6 ∧ s6.rip = a0 + 28 ∧ s6.mem = s.mem ∧
      (∀ i : Fin 16, i.val ≠ 2 → s6.regs i = s5.regs i) ∧ s6.low8 2 = s5.low8 2 <<< 3 := by
    have d : decode s5.mem s5.rip = some (.shlB 2 3, 3) := by
      rw [m5, r5]; exact dec_shlDl s.mem a0 hcode
    obtain ⟨a, b, c, e, f⟩ := exec_shlB_facts 2 3 (by decide) 3 s5
    refine ⟨_, step_of_decode s5 _ _ d, ?_, ?_, c, ?_⟩
    · rw [a, r5]
    · rw [b, m5]
    · rw [e, c3]
  have hdl : s6.low8 2 = BitVec.ofNat 8 (toggle P.1) <<< 3 := by
    rw [l6, l5, k4, l4, l3, k3, l2]
    rw [← toggle_byte P.1]
  -- 7: XOR [opcode byte],DL
  have hea : ripEA s6.rip 6 (BitVec.ofInt 32 (-22)) = a0 + 12 := by
    have : (BitVec.ofInt 32 (-22)).toInt = -22 := by decide
    unfold ripEA; rw [r6, this, Int.ofNat_eq_natCast]; omega
  obtain ⟨s7, e7, r7, m7, g7⟩ : ∃ s7, step s6 = some s7 ∧ s7.rip = a0 + 34 ∧
      s7.mem = wr8 s.mem (a0 + 12) (s.mem (a0 + 12) ^^^ (BitVec.ofNat 8 (toggle P.1) <<< 3)) ∧
      (∀ i, s7.regs i = s6.regs i) := by
    have d : decode s6.mem s6.rip = some (.xorMB (BitVec.ofInt 32 (-22)) 2, 6) := by
      rw [m6, r6]; exact dec_xorM s.mem a0 hcode
    refine ⟨_, step_of_decode s6 _ _ d, ?_, ?_, fun i => rfl⟩
    · show s6.rip + 6 = _
      rw [r6]
    · show wr8 s6.mem (ripEA s6.rip 6 (BitVec.ofInt 32 (-22))) _ = _
      rw [hea, m6, hdl]
  have hcode7 : CodeOk s7.mem a0 := by
    rw [m7]; exact codeOk_wr8 s.mem a0 _ hcode
  -- 8: LEA RSI,[RSI+8]
  obtain ⟨s8, e8, r8, m8, n8, g8⟩ : ∃ s8, step s7 = some s8 ∧ s8.rip = a0 + 38 ∧ s8.mem = s7.mem ∧
      s8.regs 6 = s7.regs 6 + 8 ∧ (∀ i, i ≠ 6 → s8.regs i = s7.regs i) := by
    have d : decode s7.mem s7.rip = some (.leaD 6 6 8, 4) := by
      rw [r7]; exact dec_leaRsi s7.mem a0 hcode7
    have sx : (8 : BitVec 8).signExtend 64 = 8 := by decide
    refine ⟨_, step_of_decode s7 _ _ d, ?_, rfl, ?_, ?_⟩
    · show s7.rip + 4 = _
      rw [r7]
    · rw [exec_leaD, sx]; simp [St.setReg]
    · intro i hi; rw [exec_leaD]; simp [St.setReg, hi]
  -- 9: CMP RDI,RSI
  obtain ⟨s9, e9, r9, m9, f9, g9⟩ : ∃ s9, step s8 = some s9 ∧ s9.rip = a0 + 41 ∧ s9.mem = s7.mem ∧
      s9.fl = (aluW 7 (s8.regs 7) (s8.regs 6) s8.fl.cf).2 ∧ (∀ i, s9.regs i = s8.regs i) := by
    have d : decode s8.mem s8.rip = some (.alu 7 7 6, 3) := by
      rw [m8, r8]; exact dec_cmpRdi s7.mem a0 hcode7
    have ex : exec (.alu 7 7 6) 3 s8 =
        { s8 with rip := s8.rip + 3, fl := (aluW 7 (s8.regs 7) (s8.regs 6) s8.fl.cf).2 } := by simp [exec]
    refine ⟨_, step_of_decode s8 _ _ d, ?_, ?_, ?_, fun i => ?_⟩ <;> rw [ex]
    · show s8.rip + 3 = _; rw [r8]
    · exact m8
  -- 10: JG back to the ADC
  have hrel : (-32 : Int) = (0xE0 : BitVec 8).toInt := by decide
  obtain ⟨s10, e10, g10, m10, f10, tk, nt⟩ : ∃ s10, step s9 = some s10 ∧ (∀ i, s10.regs i = s9.regs i) ∧
      s10.mem = s9.mem ∧ s10.fl = s9.fl ∧ (cond 15 s9.fl = true → s10.rip = a0 + 11) ∧
      (cond 15 s9.fl = false → s10.rip = a0 + 43) := by
    have d : decode s9.mem s9.rip = some (.jcc 15 0xE0, 2) := by
      rw [m9, r9]; exact dec_jg s7.mem a0 hcode7
    obtain ⟨a, b, c, d', e'⟩ := exec_jcc_facts 15 0xE0 2 s9
    refine ⟨_, step_of_decode s9 _ _ d, fun i => by rw [a], b, c, fun h => ?_, fun h => ?_⟩
    · rw [d' h, r9, ← hrel, Int.ofNat_eq_natCast]; omega
    · rw [e' h, r9]
  have hrun : run 10 s = some s10 := by
    rw [run_succ_some 9 s s1 e1, run_succ_some 8 s1 s2 e2, run_succ_some 7 s2 s3 e3, run_succ_some 6 s3 s4 e4,
      run_succ_some 5 s4 s5 e5, run_succ_some 4 s5 s6 e6, run_succ_some 3 s6 s7 e7, run_succ_some 2 s7 s8 e8,
      run_succ_some 1 s8 s9 e9, run_succ_some 0 s9 s10 e10]
    rfl
  -- register bookkeeping
  have chain : ∀ i : Fin 16, i.val ≠ 0 → i.val ≠ 2 → i ≠ 3 → i ≠ 6 → s10.regs i = s.regs i := by
    intro i h0 h2 h3 h6
    rw [g10, g9, g8 i h6, g7, g6 i h2, g5 i h2, g4 i h0, g3 i h0, g2 i h2, h1 i h3]
  have r3' : s10.regs 3 = s1.regs 3 := by
    rw [g10, g9, g8 3 (by decide), g7, g6 3 (by decide), g5 3 (by decide), g4 3 (by decide), g3 3 (by decide),
      g2 3 (by decide)]
  have r6' : s10.regs 6 = s.regs 6 + 8 := by
    rw [g10, g9, n8, g7, g6 6 (by decide), g5 6 (by decide), g4 6 (by decide), g3 6 (by decide),
      g2 6 (by decide), h1 6 (by decide)]
  have r7' : s10.regs 7 = s.regs 7 := chain 7 (by decide) (by decide) (by decide) (by decide)
  have r8' : s10.regs 8 = s.regs 8 := chain 8 (by decide) (by decide) (by decide) (by decide)
  -- the comparison
  have hb : (s.regs 6 + 8).toNat = (s.regs 6).toNat + 8 := by
    rw [BitVec.toNat_add]
    have : (8 : BitVec 64).toNat = 8 := by decide
    rw [this]; omega
  have e7' : s8.regs 7 = s.regs 7 := by
    rw [g8 7 (by decide), g7, g6 7 (by decide), g5 7 (by decide), g4 7 (by decide), g3 7 (by decide),
      g2 7 (by decide), h1 7 (by decide)]
  have e6' : s8.regs 6 = s.regs 6 + 8 := by
    rw [n8, g7, g6 6 (by decide), g5 6 (by decide), g4 6 (by decide), g3 6 (by decide), g2 6 (by decide),
      h1 6 (by decide)]
  have hjg := jg_after_cmp (s8.regs 7) (s8.regs 6) s8.fl.cf (by rw [e7']; exact he) (by rw [e6', hb]; omega)
  rw [e7', e6', hb] at hjg
  have hc15 : cond 15 s9.fl = true ↔ (s10.regs 6).toNat < (s10.regs 7).toNat := by
    rw [f9, e7', e6', r6', r7', hb]; exact hjg.1
  have hF7 : (F = 7) ↔ aluField (s.mem (a0 + 12)) = 7 := by rw [hF]; exact fin8_ofNat_eq7 _
  refine ⟨s10, hrun, ?_, ?_, r6', r7', r8', ?_, ?_, ?_⟩
  · rw [r3', g1]
    unfold staticStep kAlu
    dsimp only
    rw [← hF, ← hP]
    by_cases hh : F = 7
    · simp [hh, hF7.1 hh]
    · simp [hh, mt hF7.2 hh]
  · rw [m10, m9, m7]
    unfold staticStep kAlu
    dsimp only
    rw [← hF, ← hP]
  · intro hlt
    have hc := hc15.2 hlt
    refine ⟨tk hc, ?_⟩
    have hc' : cond 15 (aluW 7 (s.regs 7) (s.regs 6 + 8) s8.fl.cf).2 = true := by
      have := hc; rwa [f9, e7', e6'] at this
    rw [f10, f9, e7', e6']
    exact hjg.2 hc'
  · intro hlt
    have hc : cond 15 s9.fl = false := by
      cases h : cond 15 s9.fl
      · rfl
      · exact absurd (hc15.1 h) hlt
    exact nt hc
  · rw [trace_succ_some 9 s s1 e1, trace_succ_some 8 s1 s2 e2, trace_succ_some 7 s2 s3 e3,
      trace_succ_some 6 s3 s4 e4, trace_succ_some 5 s4 s5 e5, trace_succ_some 4 s5 s6 e6,
      trace_succ_some 3 s6 s7 e7, trace_succ_some 2 s7 s8 e8, trace_succ_some 1 s8 s9 e9,
      trace_succ_some 0 s9 s10 e10]
    rw [hrip, r1, r2, r3, r4, r5, r6, r7, r8, r9]
    rfl

end SmcTamper
