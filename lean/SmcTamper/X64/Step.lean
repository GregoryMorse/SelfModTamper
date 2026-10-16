module
public import SmcTamper.Spec.Step

@[expose] public section

namespace SmcTamper

theorem fin8_val3 : (3 : Fin 8).val = 3 := rfl
theorem fin8_val2 : (2 : Fin 8).val = 2 := rfl
theorem fin8_val0 : (0 : Fin 8).val = 0 := rfl
theorem fin8_val5 : (5 : Fin 8).val = 5 := rfl
theorem fin8_val7 : (7 : Fin 8).val = 7 := rfl
theorem fin16_val15 : (15 : Fin 16).val = 15 := rfl

/-- Runs compose. -/
theorem run_add (a b : Nat) (s : St) : run (a + b) s = (run a s).bind (run b) := by
  induction a generalizing s with
  | zero => simp [run]
  | succ a ih =>
    rw [Nat.succ_add]
    simp only [run]
    cases step s with
    | none => rfl
    | some t => simpa using ih t

theorem run_one (s : St) : run 1 s = step s := by simp [run]

theorem step_of_decode (s : St) (i : Instr) (len : Nat) (h : decode s.mem s.rip = some (i, len)) :
    step s = some (exec i len s) := by simp [step, h]

/-- ADC with the carry flag clear is ADD (the kernels clear CF before every ADC). -/
theorem aluW_adc_clear {w : Nat} (a b : BitVec w) : aluW 2 a b false = aluW 0 a b false := by
  simp [aluW]

/-- SBB with the carry flag clear is SUB. -/
theorem aluW_sbb_clear {w : Nat} (a b : BitVec w) : aluW 3 a b false = aluW 5 a b false := by
  simp [aluW, fin8_val3, fin8_val5]

/-- C19: the condition codes used by the kernels (Table 3). -/
theorem cond_S (fl : Flags) : cond 8 fl = fl.sf := rfl
theorem cond_P (fl : Flags) : cond 10 fl = fl.pf := rfl
theorem cond_G (fl : Flags) : cond 15 fl = (!fl.zf && (fl.sf == fl.ovf)) := rfl
theorem cond_L (fl : Flags) : cond 12 fl = (fl.sf != fl.ovf) := rfl

/-- The signed/unsigned compare lemma behind the loop of `TPComp` (`CMP RDI,RSI; JG`): for addresses below `2^63`,
`JG` is taken exactly when `RSI < RDI`, and then CF is clear, so ADC is ADD in the next iteration. -/
theorem jg_after_cmp (a b : BitVec 64) (c : Bool) (ha : a.toNat < 2 ^ 63) (hb : b.toNat < 2 ^ 63) :
    (cond 15 (aluW 7 a b c).2 = true ↔ b.toNat < a.toNat) ∧
    (cond 15 (aluW 7 a b c).2 = true → (aluW 7 a b c).2.cf = false) := by
  have msa : a.msb = false := by
    rw [BitVec.msb_eq_decide]; simp; omega
  have msb' : b.msb = false := by
    rw [BitVec.msb_eq_decide]; simp; omega
  have hsub := BitVec.toNat_sub a b
  have hlt := BitVec.isLt (a - b)
  simp only [aluW, cond, fin8_val7, fin16_val15] at *
  have mss : (a - b).msb = decide (2 ^ 63 ≤ (a - b).toNat) := by rw [BitVec.msb_eq_decide]
  have hz : (a - b = 0) ↔ a.toNat = b.toNat := by
    constructor
    · intro h; have := congrArg BitVec.toNat h; simp at this; omega
    · intro h; apply BitVec.eq_of_toNat_eq; simp; omega
  simp only [sf, msa, msb', mss, Bool.false_eq_true, bne_self_eq_false, Bool.false_and, Bool.false_eq, beq_false,
    Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq, decide_eq_false_iff_not, hz]
  omega

/-! One-step lemmas for the forms of the kernels (C19, C22). -/

theorem exec_clc (len : Nat) (s : St) : exec .clc len s = { s with rip := s.rip + len, fl := { s.fl with cf := false } } := rfl

theorem exec_leaD (d b : Fin 16) (x : BitVec 8) (len : Nat) (s : St) :
    exec (.leaD d b x) len s = ({ s with rip := s.rip + len }).setReg d (s.regs b + x.signExtend 64) := rfl

theorem exec_setcc (cc : Fin 16) (r : Fin 4) (len : Nat) (s : St) :
    exec (.setcc cc r) len s = ({ s with rip := s.rip + len }).setLow8 r (if cond cc s.fl then 1 else 0) := rfl

/-- C22: a `[rip + disp32]` operand is addressed relative to the end of the instruction: the byte patched by
`XOR BYTE PTR [rip+disp], r8` is at `rip + len + sext(disp)`. -/
theorem exec_xorMB_mem (disp : BitVec 32) (r : Fin 4) (len : Nat) (s : St) :
    (exec (.xorMB disp r) len s).mem = wr8 s.mem (ripEA s.rip len disp) (s.mem (ripEA s.rip len disp) ^^^ s.low8 r) := rfl

/-- ADC executed with CF clear behaves as ADD (register-memory form used by the kernels). -/
theorem exec_adc_clear (d b : Fin 16) (len : Nat) (s : St) (h : s.fl.cf = false) :
    exec (.aluM 2 d b) len s = exec (.aluM 0 d b) len s := by
  simp only [exec, h, aluW_adc_clear]
  rfl

end SmcTamper
