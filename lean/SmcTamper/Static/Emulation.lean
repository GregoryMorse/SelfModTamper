module
public import SmcTamper.Spec.Kernel
public import SmcTamper.Spec.CModel
public import SmcTamper.Bits.Bytes
public import SmcTamper.Bits.Parity
public import SmcTamper.Bits.Opcode
public import SmcTamper.X64.Step

@[expose] public section

namespace SmcTamper

theorem signK_bit (res : BitVec 64) (i : Nat) :
    (res &&& 0x8000000000000000#64).getLsbD i = (decide (i = 63) && res.getLsbD i) := by
  have hK : (0x8000000000000000#64) = (1#64 <<< 63) := by decide
  rw [hK, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft]
  by_cases h : i = 63
  · subst h; simp
  · by_cases hl : i < 63
    · have : decide (i < 63) = true := by simpa using hl
      simp [h, this]
    · have h1 : (1#64).getLsbD (i - 63) = false := by
        rw [BitVec.getLsbD_one]
        have : decide (i - 63 = 0) = false := by simp; omega
        simp [this]
      simp [h, h1]

theorem and_signbit_ne_zero (res : BitVec 64) : (res &&& 0x8000000000000000#64 != 0) = res.msb := by
  have hmsb : res.msb = res.getLsbD 63 := BitVec.msb_eq_getLsbD_last res
  rw [hmsb]
  have hk := fun i => signK_bit res i
  cases hm : res.getLsbD 63
  · have : res &&& 0x8000000000000000#64 = 0 := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have z : (0 : BitVec 64).getLsbD i = false := by simp
      rw [hk i, z]
      by_cases h63 : i = 63
      · subst h63; rw [hm]; simp
      · simp [h63]
    rw [this]; simp
  · have : res &&& 0x8000000000000000#64 ≠ 0 := by
      intro h
      have h2 := congrArg (fun x => x.getLsbD 63) h
      simp only [hk, BitVec.getLsbD_zero, hm] at h2
      simp at h2
    simpa using this

theorem cOpNext_eq (op : Nat) (res : BitVec 64) : cOpNext op res = op ^^^ toggle res := by
  unfold cOpNext toggle
  rw [and_signbit_ne_zero, ← not_paritybyteC_eq_pf]
  simp only [sf]
  generalize paritybyteC (res.setWidth 8) = a
  cases a <;> by_cases hb : res.msb = true <;> simp [hb]

theorem fin3 : ((3 : Fin 8) : Nat) = 3 := rfl
theorem fin6 : ((6 : Fin 8) : Nat) = 6 := rfl

theorem kAlu_opcodeOf (op : Nat) (hop : IsOp op) (sum d : BitVec 64) :
    kAlu (opcodeOf op) sum d = cSwitch op sum d := by
  rcases hop with rfl | rfl | rfl | rfl
  · have h : aluField (opcodeOf 0) = 2 := by decide
    simp [kAlu, h, aluW, cSwitch, Fin.ofNat, fin3, fin6]
  · have h : aluField (opcodeOf 1) = 3 := by decide
    simp [kAlu, h, aluW, cSwitch, Fin.ofNat, fin3, fin6]
  · have h : aluField (opcodeOf 4) = 6 := by decide
    simp [kAlu, h, aluW, cSwitch, Fin.ofNat, fin3, fin6]
  · have h : aluField (opcodeOf 5) = 7 := by decide
    simp [kAlu, h, aluW, cSwitch, Fin.ofNat, fin3, fin6]

/-- Coupling of the Level-1 machine to the C model over the original memory image `m`. -/
structure Inv (m : Mem) (opAddr : Nat) (k : KState) (c : CState) : Prop where
  mem : k.mem = wr8 m opAddr (opcodeOf c.op)
  ptr : k.ptr = c.p
  sum : k.sum = c.sum
  op : IsOp c.op
  al : c.p % 8 = 0

theorem data_read (m : Mem) (opAddr p op : Nat) (hop : IsOp op) (hK : IsKernelOpcode (m opAddr)) (hp : p % 8 = 0) :
    rd64 (wr8 m opAddr (opcodeOf op)) p =
      (if p = opAddr / 8 * 8 then cSubst (rd64 m p) (opAddr % 8) op else rd64 m p) := by
  by_cases h : p = opAddr / 8 * 8
  · rw [if_pos h, h, rd64_wr8_aligned, cSubst_eq_setByte _ _ (by omega) op hop]
    rw [byteAt_rd64 _ _ _ (by omega)]
    have : opAddr / 8 * 8 + opAddr % 8 = opAddr := by omega
    rw [this]; exact hK
  · rw [if_neg h]
    apply rd64_wr8_outside
    omega

theorem step_match (m : Mem) (opAddr : Nat) (hK : IsKernelOpcode (m opAddr)) (k : KState) (c : CState)
    (hI : Inv m opAddr k c) : Inv m opAddr (staticStep opAddr k) (tpCompCStep m opAddr c) := by
  obtain ⟨hm, hp, hs, ho, ha⟩ := hI
  have hd := data_read m opAddr c.p c.op ho hK ha
  have hkal := kAlu_opcodeOf c.op ho c.sum
  unfold staticStep tpCompCStep
  simp only [hm, hp, hs]
  have hb : wr8 m opAddr (opcodeOf c.op) opAddr = opcodeOf c.op := by simp [wr8]
  rw [hb, hd, hkal]
  refine ⟨?_, rfl, rfl, ?_, ?_⟩
  · show wr8 _ _ _ = _
    rw [wr8_wr8_same, cOpNext_eq, opcodeOf_xor_toggle _ ho]
  · simp only [cOpNext_eq]; exact isOp_xor_toggle _ ho _
  · simp only; omega

theorem iter_match (m : Mem) (opAddr : Nat) (hK : IsKernelOpcode (m opAddr)) (n : Nat) :
    ∀ (k : KState) (c : CState), Inv m opAddr k c →
      Inv m opAddr (staticRun opAddr n k) (tpCompCIter m opAddr n c) := by
  induction n with
  | zero => intro k c h; exact h
  | succ n ih => intro k c h; exact ih _ _ (step_match m opAddr hK k c h)

/-- **Level 1 ≡ the C model (Fig. 2 ≡ Fig. 3).** Starting from the original image `m` (opcode byte `m opAddr` one of
the four kernel opcodes, equal to `opcodeOf op0`), an aligned data pointer and any initial sum, the static SMC
kernel and the transcribed C loop compute the same sum, end with the same persistent operation number, and the
kernel's final opcode byte is `opcodeOf` of it. -/
theorem static_eq_c (m : Mem) (opAddr p0 size op0 : Nat) (hK : IsKernelOpcode (m opAddr)) (hop : IsOp op0)
    (h0 : m opAddr = opcodeOf op0) (hal : p0 % 8 = 0) :
    let k := staticRun opAddr ((size + 7) / 8) ⟨m, p0, 0⟩
    let c := tpCompC m opAddr p0 size op0
    k.sum = c.1 ∧ IsOp c.2 ∧ k.mem = wr8 m opAddr (opcodeOf c.2) := by
  intro k c
  have := iter_match m opAddr hK ((size + 7) / 8) ⟨m, p0, 0⟩ ⟨p0, 0, op0⟩
    ⟨by
      show m = wr8 m opAddr (opcodeOf op0)
      funext x; by_cases h : x = opAddr <;> simp [wr8, h, h0], rfl, rfl, hop, hal⟩
  exact ⟨this.sum, this.op, this.mem⟩

end SmcTamper
