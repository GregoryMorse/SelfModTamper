module
public import SmcTamper.Unrolled.Adjust

@[expose] public section

namespace SmcTamper

set_option linter.unusedVariables false

/-! ## Level 1 unrolled kernel ≡ `TPCompCLoop` -/

/-- Byte `j` of a mask word. -/
def maskByte (v : BitVec 64) (j : Nat) : BitVec 8 := (v >>> (8 * j)).setWidth 8

/-- The memory `M` with the XOR of `v` applied at `pa` is unchanged at address `x` when no mask byte covers `x`. -/
def Untouched (pa : Nat) (v : BitVec 64) (x : Nat) : Prop := ∀ j, j < 8 → x = pa + j → maskByte v j = 0

theorem xorQword_apply (M : Mem) (pa : Nat) (v : BitVec 64) (x : Nat) (h : Untouched pa v x) :
    xorQword M pa v x = M x := by
  unfold xorQword
  by_cases hw : pa ≤ x ∧ x < pa + 8
  · rw [if_pos hw]
    have := h (x - pa) (by omega) (by omega)
    unfold maskByte at this
    rw [this]; simp
  · rw [if_neg hw]

theorem xorQword_zero (M : Mem) (pa : Nat) : xorQword M pa 0 = M := by
  funext x; unfold xorQword; split <;> simp

theorem xorQword_twice (M : Mem) (pa : Nat) (v : BitVec 64) : xorQword (xorQword M pa v) pa v = M := by
  funext x; unfold xorQword
  by_cases hw : pa ≤ x ∧ x < pa + 8
  · simp only [if_pos hw]
    generalize (v >>> (8 * (x - pa))).setWidth 8 = b
    rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  · simp only [hw, if_false]

theorem xorQword_wr8 (M : Mem) (pa : Nat) (v : BitVec 64) (a : Nat) (y : BitVec 8) (h : Untouched pa v a) :
    xorQword (wr8 M a y) pa v = wr8 (xorQword M pa v) a y := by
  funext x
  by_cases hx : x = a
  · subst hx
    rw [xorQword_apply _ _ _ _ h]
    unfold xorQword
    by_cases hw : pa ≤ x ∧ x < pa + 8
    · have := h (x - pa) (by omega) (by omega)
      unfold maskByte at this
      simp [wr8, this]
    · simp [wr8, hw]
  · unfold xorQword wr8
    simp [hx]

theorem rd64_xorQword (M : Mem) (pa : Nat) (v : BitVec 64) (p : Nat) (h : ∀ k, k < 8 → Untouched pa v (p + k)) :
    rd64 (xorQword M pa v) p = rd64 M p :=
  rd64_congr _ _ p (fun k hk => xorQword_apply M pa v (p + k) (h k hk))


/-- Coupling of the Level-1 state to the C-loop state; the memory is the image `m` with the opcode bytes of the C `op`
array, and the XOR of `v` at `pa` applied (the termination patch during the final pass; `v = 0` otherwise). -/
structure UInv (base : Nat) (m : Mem) (pa : Nat) (v : BitVec 64) (u : Nat) (k : KState) (c : CLState) : Prop where
  mem : k.mem = xorQword (opsMem base m c.op) pa v
  ptr : k.ptr = c.p
  sum : k.sum = c.sum
  ops : ∀ i, i < 296 → IsOp (c.op i)
  al : c.p % 8 = 0
  lc : c.lc = u ∨ (c.lc = 296 ∧ u = 0)
  ult : u < 296

theorem unit_step_match (base : Nat) (m : Mem) (pa : Nat) (v : BitVec 64) (u : Nat) (k : KState) (c : CLState)
    (hI : UInv base m pa v u k c) (hK : ∀ w, w < 296 → IsKernelOpcode (m (base + opOff w)))
    (hP : ∀ w, w < 296 → Untouched pa v (base + opOff w)) (hD : ∀ j, j < 8 → Untouched pa v (c.p + j)) :
    UInv base m pa v ((u + 1) % 296) (unitStep base u k) (tpCompCLoopStep m base c) := by
  obtain ⟨hm, hp, hs, ho, ha, hl, hu⟩ := hI
  have hp148 : perPage = 148 := perPage_148
  have hn296 : numUnits = 296 := numUnits_296
  have hlc : (if c.lc = 296 then 0 else c.lc) = u := by
    rcases hl with h | ⟨h1, h2⟩
    · rw [h]; split <;> omega
    · rw [h1, h2]; simp
  obtain ⟨t, ht⟩ : ∃ t, t = (u + 148) % 296 := ⟨_, rfl⟩
  have htl : t < 296 := by omega
  have hread : k.mem (base + opOff u) = opcodeOf (c.op u) := by
    rw [hm, xorQword_apply _ _ _ _ (hP u hu), opsMem_at base m c.op u (by omega)]
  have hdata : rd64 k.mem k.ptr =
      (match adjustFind base c.p with
       | some (bi, idx) => cSubst (rd64 m c.p) bi (c.op idx)
       | none => rd64 m c.p) := by
    rw [hm, hp, rd64_xorQword _ _ _ _ hD, rd64_opsMem base m c.op c.p hK ho ha]
    rfl
  have hrt : k.mem (base + opOff t) = opcodeOf (c.op t) := by
    rw [hm, xorQword_apply _ _ _ _ (hP t htl), opsMem_at base m c.op t (by omega)]
  have hkal : ∀ d, kAlu (opcodeOf (c.op u)) c.sum d = cSwitch (c.op u) c.sum d :=
    fun d => kAlu_opcodeOf (c.op u) (ho u hu) c.sum d
  unfold unitStep tpCompCLoopStep
  simp only [hlc, hread, hkal, hdata, hs, hp148, hn296]
  rw [← ht]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show wr8 k.mem _ _ = _
    rw [hrt, ← opcodeOf_xor_toggle _ (ho t htl), hm, ← xorQword_wr8 _ _ _ _ _ (hP t htl),
      opsMem_upd base m c.op t _ htl, cOpNext_eq]
    rfl
  · simp [hp]
  · rfl
  · intro i hi
    simp only
    split
    · rw [cOpNext_eq]; exact isOp_xor_toggle _ (ho t htl) _
    · exact ho i hi
  · simp only; omega
  · simp only; omega
  · omega

end SmcTamper
