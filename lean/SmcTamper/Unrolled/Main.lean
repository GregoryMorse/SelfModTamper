module
public import SmcTamper.Unrolled.Patch

@[expose] public section

namespace SmcTamper

set_option linter.unusedVariables false

theorem tpCompCLoopIter_add (m : Mem) (base a b : Nat) (c : CLState) :
    tpCompCLoopIter m base (a + b) c = tpCompCLoopIter m base b (tpCompCLoopIter m base a c) := by
  induction a generalizing c with
  | zero => simp [tpCompCLoopIter]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [tpCompCLoopIter]
    exact ih _


theorem untouched_zero (x : Nat) : Untouched 0 0 x := by
  intro j hj _; unfold maskByte; simp

theorem units_match (base : Nat) (m : Mem) (pa : Nat) (v : BitVec 64)
    (hK : ∀ w, w < 296 → IsKernelOpcode (m (base + opOff w)))
    (hP : ∀ w, w < 296 → Untouched pa v (base + opOff w)) :
    ∀ (n u : Nat) (k : KState) (c : CLState), UInv base m pa v u k c →
      (∀ i, i < n → ∀ j, j < 8 → Untouched pa v (c.p + 8 * i + j)) →
      UInv base m pa v ((u + n) % 296) (unitsFrom base u n k) (tpCompCLoopIter m base n c) := by
  intro n
  induction n with
  | zero => intro u k c h _; simpa [unitsFrom, tpCompCLoopIter, Nat.mod_eq_of_lt h.ult] using h
  | succ n ih =>
    intro u k c h hD
    have h1 := unit_step_match base m pa v u k c h hK hP (fun j hj => by simpa using hD 0 (by omega) j hj)
    have := ih ((u + 1) % 296) (unitStep base u k) (tpCompCLoopStep m base c) h1
      (fun i hi j hj => by
        have := hD (i + 1) (by omega) j hj
        show Untouched pa v (c.p + 8 + 8 * i + j)
        rw [show c.p + 8 + 8 * i + j = c.p + 8 * (i + 1) + j by omega]
        exact this)
    simp only [unitsFrom, tpCompCLoopIter]
    rw [show (u + (n + 1)) % 296 = ((u + 1) % 296 + n) % 296 by omega]
    exact this

theorem passes_match (base : Nat) (m : Mem) (hK : ∀ w, w < 296 → IsKernelOpcode (m (base + opOff w))) :
    ∀ (q : Nat) (k : KState) (c : CLState), UInv base m 0 0 0 k c →
      UInv base m 0 0 0 (fullPasses base q k) (tpCompCLoopIter m base (296 * q) c) := by
  intro q
  induction q with
  | zero => intro k c h; simpa [fullPasses, tpCompCLoopIter] using h
  | succ q ih =>
    intro k c h
    have h1 := units_match base m 0 0 hK (fun w _ => untouched_zero _) 296 0 k c h (fun i _ j _ => untouched_zero _)
    simp only [Nat.zero_add, show 296 % 296 = 0 by rfl] at h1
    have := ih _ _ h1
    simp only [fullPasses]
    rw [show 296 * (q + 1) = 296 + 296 * q by omega, tpCompCLoopIter_add]
    exact this


theorem tpCompCLoopIter_p (m : Mem) (base : Nat) : ∀ (n : Nat) (c : CLState), (tpCompCLoopIter m base n c).p = c.p + 8 * n := by
  intro n
  induction n with
  | zero => intro c; simp [tpCompCLoopIter]
  | succ n ih => intro c; simp only [tpCompCLoopIter]; rw [ih]; show c.p + 8 + 8 * n = _; omega

/-- **Level 1 unrolled kernel ≡ `TPCompCLoop`.** Let the image `m` hold, at each of the 296 opcode addresses
`base + opOff u`, the kernel opcode `opcodeOf (ops0 u)` (the persistent `op` array of the C emulation); let the data
pointer be 8-aligned and `size` a positive multiple of 8; assume the final pass reads no qword that overlaps the five
patched bytes (`hno`). Then one call of the Level-1 machine (full passes, termination patch, final units, epilogue) and the
C loop agree on the sum; the C `op` array stays in `{0,1,4,5}`; and the machine's memory afterwards is the image with the
opcode bytes of the C loop's final `op` array and nothing else changed (the patch is fully undone). -/
theorem unrolled_emulation (base : Nat) (m : Mem) (ops0 : Nat → Nat) (p0 size : Nat)
    (hops : ∀ u, u < 296 → IsOp (ops0 u)) (hmem : ∀ u, u < 296 → m (base + opOff u) = opcodeOf (ops0 u))
    (hal : p0 % 8 = 0) (h8 : size % 8 = 0) (hpos : 8 ≤ size)
    (hno : ∀ i, i < finalUnits size → ∀ k j, k < 8 → j < 5 →
      p0 + 2368 * passCount size + 8 * i + k ≠ patchAddr base (finalUnits size) + j) :
    (callUnrolled base size ⟨m, p0, 0⟩).sum = (tpCompCLoop m base p0 size ops0).sum ∧
    (∀ u, u < 296 → IsOp ((tpCompCLoop m base p0 size ops0).op u)) ∧
    (callUnrolled base size ⟨m, p0, 0⟩).mem = opsMem base m (tpCompCLoop m base p0 size ops0).op := by
  have hK : ∀ w, w < 296 → IsKernelOpcode (m (base + opOff w)) := fun w hw => by
    rw [hmem w hw]; exact (isKernelOpcode_iff _).2 ⟨_, hops w hw, rfl⟩
  -- the count decomposition
  obtain ⟨q, hq⟩ : ∃ q, q = passCount size := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n, n = finalUnits size := ⟨_, rfl⟩
  have hq' : 2368 * q ≤ size - 1 ∧ size - 1 < 2368 * (q + 1) := by
    rw [hq]; unfold passCount; omega
  have hn' : n = (size - 2368 * q) / 8 := by rw [hn, hq]; rfl
  have hn1 : 1 ≤ n := by omega
  have hn2 : n ≤ 296 := by omega
  have hcount : (size + 7) / 8 = 296 * q + n := by omega
  unfold callUnrolled tpCompCLoop
  dsimp only
  rw [← hq, ← hn, hcount, tpCompCLoopIter_add]
  -- initial coupling
  have h0 : UInv base m 0 0 0 (⟨m, p0, 0⟩ : KState) (⟨p0, 0, 0, ops0⟩ : CLState) := by
    refine ⟨?_, rfl, rfl, hops, hal, Or.inl rfl, by omega⟩
    show m = xorQword (opsMem base m ops0) 0 0
    rw [xorQword_zero, opsMem_self base m ops0 hmem]
  have hpass := passes_match base m hK q _ _ h0
  obtain ⟨hpm, hpp, hps, hpo, hpa, hpl, _⟩ := hpass
  -- the patch
  obtain ⟨pa, hpa'⟩ : ∃ pa, pa = patchAddr base n := ⟨_, rfl⟩
  obtain ⟨pv, hpv⟩ : ∃ pv, pv = patchVal n := ⟨_, rfl⟩
  have hP : ∀ w, w < 296 → Untouched pa pv (base + opOff w) := by
    intro w hw j hj he
    by_cases h5 : 5 ≤ j
    · rw [hpv]; exact patchVal_high n j h5 hj
    · exfalso
      have := patch_not_opcode n w j hn1 hn2 hw (by omega)
      simp only [hpa', patchAddr] at he
      omega
  have hp_eq : (tpCompCLoopIter m base (296 * q) ⟨p0, 0, 0, ops0⟩).p = p0 + 2368 * q := by
    rw [tpCompCLoopIter_p]; show p0 + 8 * (296 * q) = _; omega
  have h1 : UInv base m pa pv 0 { fullPasses base q ⟨m, p0, 0⟩ with
        mem := xorQword (fullPasses base q ⟨m, p0, 0⟩).mem pa pv } (tpCompCLoopIter m base (296 * q) ⟨p0, 0, 0, ops0⟩) := by
    refine ⟨?_, hpp, hps, hpo, hpa, hpl, by omega⟩
    show xorQword (fullPasses base q ⟨m, p0, 0⟩).mem pa pv = _
    rw [hpm, xorQword_zero]
  have hD : ∀ i, i < n → ∀ j, j < 8 → Untouched pa pv ((tpCompCLoopIter m base (296 * q) ⟨p0, 0, 0, ops0⟩).p + 8 * i + j) := by
    intro i hi j hj j' hj' he
    by_cases h5 : 5 ≤ j'
    · rw [hpv]; exact patchVal_high n j' h5 hj'
    · exfalso
      rw [hp_eq] at he
      exact hno i (by rw [← hn]; exact hi) j j' hj (by omega) (by rw [← hn, hpa'] at *; omega)
  have h2 := units_match base m pa pv hK hP n 0 _ _ h1 hD
  rw [← hpa', ← hpv]
  refine ⟨h2.sum, h2.ops, ?_⟩
  show xorQword (unitsFrom base 0 n _).mem pa pv = _
  rw [h2.mem, xorQword_twice]

end SmcTamper
