module
public import SmcTamper.Unrolled.L2Chain

@[expose] public section

namespace SmcTamper

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Level 2 of the unrolled kernel, part 5: one full pass of `TPCompLoop`

A full pass runs from the loop head `L0` (offset 9: `sub rdi, 2368; jg`) through the 296 units to the `jmp L0` at the end of the
epilogue; it executes `2377 = 2 + 1 + 2373 + 1` instructions. -/

theorem aluW_sub_cmp {w : Nat} (a b : BitVec w) (c : Bool) : aluW 5 a b c = aluW 7 a b c := by
  simp [aluW]

theorem fin16_val12 : (12 : Fin 16).val = 12 := rfl

theorem jl_after_cmp (a b : BitVec 64) (c : Bool) (ha : a.toNat < 2 ^ 63) (hb : b.toNat < 2 ^ 63) :
    cond 12 (aluW 7 a b c).2 = true ↔ a.toNat < b.toNat := by
  have msa : a.msb = false := by
    rw [BitVec.msb_eq_decide]; simp; omega
  have msb' : b.msb = false := by
    rw [BitVec.msb_eq_decide]; simp; omega
  have hsub := BitVec.toNat_sub a b
  have hlt := BitVec.isLt (a - b)
  simp only [aluW, cond, fin8_val7, fin16_val12] at *
  have mss : (a - b).msb = decide (2 ^ 63 ≤ (a - b).toNat) := by rw [BitVec.msb_eq_decide]
  simp only [sf, msa, msb', mss, bne_self_eq_false, Bool.false_and]
  simp
  omega

theorem sdisp_add (z : Int) (r : Nat) : sdisp z + BitVec.ofNat 32 r = sdisp (z + r) := by
  unfold sdisp
  rw [BitVec.ofInt_add, BitVec.ofInt_natCast]

theorem exec_aluRI_facts (f : Fin 8) (r : Fin 16) (imm : BitVec 32) (len : Nat) (s : St) (hf : f ≠ 7) :
    (exec (.aluRI f r imm) len s).rip = s.rip + len ∧ (exec (.aluRI f r imm) len s).mem = s.mem ∧
    (exec (.aluRI f r imm) len s).fl = (aluW f (s.regs r) (imm.signExtend 64) s.fl.cf).2 ∧
    (exec (.aluRI f r imm) len s).regs r = (aluW f (s.regs r) (imm.signExtend 64) s.fl.cf).1 ∧
    (∀ i, i ≠ r → (exec (.aluRI f r imm) len s).regs i = s.regs i) := by
  unfold exec
  simp [hf, St.setReg]
  intro i hi; simp [hi]

/-- An instruction of the intro (bytes 3 .. 94) decodes from the image. -/
theorem dec_intro (enc : Instr → List Nat) (henc : EncOk enc) (base : Nat) (M : Mem) (E : Nat → Prop)
    (hI : ImgOk enc base M E) (i : Instr) (o n : Nat) (hn : (enc i).length = n) (hle : n ≤ 10) (hb : o + n ≤ 95)
    (hE : ∀ k, k < n → ¬ E (o + k)) (hsl : ∀ k, k < n → loopAt enc (o + k) = (enc i).getD k 0)
    (hr : ∀ t, decodeL (enc i ++ t) = some (i, n)) : decode M (base + o) = some (i, n) :=
  dec_img enc henc base M E hI i o n hn hle (by rw [loopLen_8123]; omega)
    (fun k hk u hu => by have := opOff_ge u; omega) hE hsl hr

/-- An instruction of the epilogue (bytes 8092 ..) decodes from the image. -/
theorem dec_tail (enc : Instr → List Nat) (henc : EncOk enc) (base : Nat) (M : Mem) (E : Nat → Prop)
    (hI : ImgOk enc base M E) (i : Instr) (o n : Nat) (hn : (enc i).length = n) (hle : n ≤ 10) (ho : 8092 ≤ o)
    (hb : o + n ≤ 8123) (hE : ∀ k, k < n → ¬ E (o + k)) (hsl : ∀ k, k < n → loopAt enc (o + k) = (enc i).getD k 0)
    (hr : ∀ t, decodeL (enc i ++ t) = some (i, n)) : decode M (base + o) = some (i, n) :=
  dec_img enc henc base M E hI i o n hn hle (by rw [loopLen_8123]; omega)
    (fun k hk u hu => by have := opOff_lt u hu; omega) hE hsl hr

theorem hr_const (enc : Instr → List Nat) (henc : EncOk enc) (i : Instr) (hi : i ∈ constInstrs) (n : Nat)
    (hn : (enc i).length = n) : ∀ t, decodeL (enc i ++ t) = some (i, n) := by
  intro t
  have := rt_const enc henc i hi t
  rwa [hn] at this

theorem toNat_sext2368 : (BitVec.signExtend 64 (2368 : BitVec 32)).toNat = 2368 := by decide +kernel
theorem sext2368 : (BitVec.signExtend 64 (2368 : BitVec 32)) = 2368 := by decide +kernel

theorem hsl_sub (enc : Instr → List Nat) (h : EncOk enc) :
    ∀ k, k < 7 → loopAt enc (9 + k) = (enc (.aluRI 5 7 2368)).getD k 0 := by
  rcases h with rfl | rfl <;> decide +kernel
theorem hsl_jg (enc : Instr → List Nat) (h : EncOk enc) :
    ∀ k, k < 2 → loopAt enc (16 + k) = (enc (.jcc 15 0x4C)).getD k 0 := by
  rcases h with rfl | rfl <;> decide +kernel
theorem hsl_clc (enc : Instr → List Nat) (h : EncOk enc) :
    ∀ k, k < 1 → loopAt enc (94 + k) = (enc .clc).getD k 0 := by
  rcases h with rfl | rfl <;> decide +kernel
theorem hsl_jmp (enc : Instr → List Nat) (h : EncOk enc) :
    ∀ k, k < 5 → loopAt enc (8092 + k) = (enc (.jmp32 (sdisp (9 - 8097)))).getD k 0 := by
  rcases h with rfl | rfl <;> decide +kernel
theorem len_sub (enc : Instr → List Nat) (h : EncOk enc) : (enc (.aluRI 5 7 2368)).length = 7 := by
  rcases h with rfl | rfl <;> rfl
theorem len_jg (enc : Instr → List Nat) (h : EncOk enc) : (enc (.jcc 15 0x4C)).length = 2 := by
  rcases h with rfl | rfl <;> rfl
theorem len_clc (enc : Instr → List Nat) (h : EncOk enc) : (enc .clc).length = 1 := by
  rcases h with rfl | rfl <;> rfl
theorem len_jmp (enc : Instr → List Nat) (h : EncOk enc) : (enc (.jmp32 (sdisp (9 - 8097)))).length = 5 := by
  rcases h with rfl | rfl <;> rfl
theorem hr_jmp (enc : Instr → List Nat) (h : EncOk enc) (d : BitVec 32) :
    ∀ t, decodeL (enc (.jmp32 d) ++ t) = some (.jmp32 d, 5) := by
  intro t; rcases h with rfl | rfl <;> exact rt_jmp32 d t

/-- The number of instructions of one full pass (`3 + (2373 + 1) = 2377`; kept symbolic so that no large numeral reaches `run`). -/
def passLen : Nat := 3 + (steps 0 296 + 1)

theorem run_chain3 (X : Nat) (s s3 s4 s5 : St) (e3 : run 3 s = some s3) (e4 : run X s3 = some s4)
    (st : step s4 = some s5) : run (3 + (X + 1)) s = some s5 := by
  rw [run_add, e3]
  simp only [Option.bind_some]
  rw [run_add, e4]
  simp only [Option.bind_some]
  rw [run_one, st]

theorem run_pass_len (s s3 s4 s5 : St) (e3 : run 3 s = some s3) (e4 : run (steps 0 296) s3 = some s4)
    (st : step s4 = some s5) : run passLen s = some s5 :=
  run_chain3 (steps 0 296) s s3 s4 s5 e3 e4 st

theorem pass_run (enc : Instr → List Nat) (henc : EncOk enc) (base : Nat) (s : St) (k : KState)
    (hrip : s.rip = base + 9) (hR1 : 2368 < (s.regs 7).toNat) (hR2 : (s.regs 7).toNat < 2 ^ 63) (hrel : Rel s k)
    (hb : k.ptr + 2368 < 2 ^ 63) (hI : ImgOk enc base s.mem (fun _ => False))
    (hK : ∀ v, v < 296 → IsKernelOpcode (s.mem (base + opOff v))) :
    ∃ s', run passLen s = some s' ∧ s'.rip = base + 9 ∧ s'.regs 7 = s.regs 7 - 2368 ∧
      Rel s' (unitsFrom base 0 296 k) ∧
      (∀ i : Fin 16, i.val ≠ 0 → i.val ≠ 1 → i.val ≠ 2 → i.val ≠ 3 → i.val ≠ 7 → s'.regs i = s.regs i) ∧
      ImgOk enc base s'.mem (fun _ => False) ∧ (∀ v, v < 296 → IsKernelOpcode (s'.mem (base + opOff v))) := by
  -- sub rdi, 2368; jg L1 (taken); clc
  obtain ⟨s3, e3, r3, m3, cf3, g3, h3⟩ : ∃ s3, run 3 s = some s3 ∧ s3.rip = base + pos 0 ∧ s3.mem = s.mem ∧
      s3.fl.cf = false ∧ (∀ i : Fin 16, i ≠ 7 → s3.regs i = s.regs i) ∧ s3.regs 7 = s.regs 7 - 2368 := by
    have d1 : decode s.mem s.rip = some (.aluRI 5 7 2368, 7) := by
      rw [hrip]
      exact dec_intro enc henc base s.mem _ hI _ 9 7 (len_sub enc henc) (by omega) (by omega)
        (fun k hk h => h) (hsl_sub enc henc)
        (hr_const enc henc _ (by simp [constInstrs]) 7 (len_sub enc henc))
    obtain ⟨a1, b1, c1, e1, f1⟩ := exec_aluRI_facts 5 7 2368 7 s (by decide)
    have st1 := step_of_decode s _ _ d1
    generalize exec (.aluRI 5 7 2368) 7 s = s1 at a1 b1 c1 e1 f1 st1
    rw [sext2368, aluW_sub_cmp] at c1 e1
    have hjg := (jg_after_cmp (s.regs 7) 2368 s.fl.cf hR2 (by decide)).1
    have hc : cond 15 s1.fl = true := by
      rw [c1]; apply hjg.2; rw [show (2368 : BitVec 64).toNat = 2368 by decide]; exact hR1
    have d2 : decode s1.mem s1.rip = some (.jcc 15 0x4C, 2) := by
      rw [b1, a1, hrip]
      exact dec_intro enc henc base s.mem _ hI _ 16 2 (len_jg enc henc) (by omega) (by omega)
        (fun k hk h => h) (hsl_jg enc henc)
        (hr_const enc henc _ (by simp [constInstrs]) 2 (len_jg enc henc))
    obtain ⟨a2, b2, c2, d2', e2⟩ := exec_jcc_facts 15 0x4C 2 s1
    have st2 := step_of_decode s1 _ _ d2
    generalize exec (.jcc 15 0x4C) 2 s1 = s2 at a2 b2 c2 d2' e2 st2
    have r2 : s2.rip = base + 94 := by
      rw [d2' hc, a1, hrip]
      have : (0x4C : BitVec 8).toInt = 76 := by decide
      rw [this]; simp only [Int.ofNat_eq_natCast]; omega
    have m2 : s2.mem = s.mem := by rw [b2, b1]
    have d3 : decode s2.mem s2.rip = some (.clc, 1) := by
      rw [m2, r2]
      exact dec_intro enc henc base s.mem _ hI _ 94 1 (len_clc enc henc) (by omega) (by omega)
        (fun k hk h => h) (hsl_clc enc henc)
        (hr_const enc henc _ (by simp [constInstrs]) 1 (len_clc enc henc))
    have st3 := step_of_decode s2 _ _ d3
    have h3 := exec_clc 1 s2
    generalize exec .clc 1 s2 = s3 at h3 st3
    have p0 := pos_spec 0
    refine ⟨s3, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [run_succ_some 2 s s1 st1, run_succ_some 1 s1 s2 st2, run_succ_some 0 s2 s3 st3]; rfl
    · rw [h3]; show s2.rip + 1 = _; rw [r2]; omega
    · rw [h3]; exact m2
    · rw [h3]
    · intro i hi; rw [h3]; show s2.regs i = _; rw [a2]; exact f1 i hi
    · rw [h3]; show s2.regs 7 = _; rw [a2, e1]; rfl
  -- the 296 units
  have hR3 : Rel s3 k := ⟨by rw [m3]; exact hrel.mem, by rw [g3 1 (by decide)]; exact hrel.ptr,
    by rw [g3 3 (by decide)]; exact hrel.sum⟩
  obtain ⟨s4, e4, r4, cf4, R4, g4, I4, K4⟩ := units_chain enc henc base (fun _ => False) 296 0 s3 k (by omega) r3 cf3
    hR3 (by omega) (by rw [m3]; exact hI) (by rw [m3]; exact hK) (fun i _ _ h => h)
  -- jmp L0
  have p296 := pos_spec (0 + 296)
  have d5 : decode s4.mem s4.rip = some (.jmp32 (sdisp (9 - 8097)), 5) := by
    rw [r4]
    have : base + pos (0 + 296) = base + 8092 := by omega
    rw [this]
    exact dec_tail enc henc base s4.mem _ I4 _ 8092 5 (len_jmp enc henc) (by omega) (by omega)
      (by omega) (fun k hk h => h) (hsl_jmp enc henc) (hr_jmp enc henc _)
  have st5 := step_of_decode s4 _ _ d5
  refine ⟨exec (.jmp32 (sdisp (9 - 8097))) 5 s4, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact run_pass_len s s3 s4 _ e3 e4 st5
  · show (Int.ofNat (s4.rip + 5) + (sdisp (9 - 8097)).toInt).toNat = _
    rw [toInt_sdisp _ (by omega) (by omega), r4]
    simp only [Int.ofNat_eq_natCast]; omega
  · show s4.regs 7 = _
    rw [g4 7 (by decide) (by decide) (by decide) (by decide), h3]
  · exact ⟨by show s4.mem = _; rw [R4.mem], R4.ptr, R4.sum⟩
  · intro i h0 h1 h2 h3' h7
    show s4.regs i = _
    rw [g4 i h0 h1 h2 h3', g3 i (fun e => h7 (by rw [e]; rfl))]
  · exact I4
  · exact K4

end SmcTamper
