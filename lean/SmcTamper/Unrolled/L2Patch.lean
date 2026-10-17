module
public import SmcTamper.Unrolled.L2Pass

@[expose] public section

namespace SmcTamper

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Level 2 of the unrolled kernel, part 6: the self-modifying triple `add dword [d], esi; xor qword [d'], rdi; sub dword [d], esi`

The intro and the epilogue each contain the same three instructions. The first one adds `ESI` to the displacement of the
second, the second applies the termination patch at the address the modified displacement names, the third restores the
displacement. The machine decodes the second instruction from the *modified* bytes. -/

theorem exec_aluMR32_mem (f : Fin 8) (disp : BitVec 32) (r : Fin 16) (len : Nat) (s : St) (hf : f ≠ 7) :
    (exec (.aluMR32 f disp r) len s).mem =
      wr32 s.mem (ripEA s.rip len disp) (aluW f (rd32 s.mem (ripEA s.rip len disp)) ((s.regs r).setWidth 32) s.fl.cf).1 := by
  unfold exec; simp [hf]

theorem exec_aluMR64_mem (f : Fin 8) (disp : BitVec 32) (r : Fin 16) (len : Nat) (s : St) (hf : f ≠ 7) :
    (exec (.aluMR64 f disp r) len s).mem =
      wr64 s.mem (ripEA s.rip len disp) (aluW f (rd64 s.mem (ripEA s.rip len disp)) (s.regs r) s.fl.cf).1 := by
  unfold exec; simp [hf]

theorem byte32_toNat (v : BitVec 32) (i : Nat) : ((v >>> (8 * i)).setWidth 8).toNat = v.toNat / 2 ^ (8 * i) % 256 := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem wr32_bytes32 (M : Mem) (a : Nat) (v : BitVec 32) (j : Nat) (hj : j < 4) :
    (wr32 M a v (a + j)).toNat = (bytes32 v).getD j 0 := by
  rw [wr32_byte M a v j hj, byte32_toNat]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> simp [bytes32]

/-- The 7 bytes of `xor qword [rip + d], rdi` at `A`, when the first three are the opcode bytes and the last four hold `d`. -/
theorem bytesAt_xorq (M : Mem) (A : Nat) (d : BitVec 32) (h0 : (M A).toNat = 0x48) (h1 : (M (A + 1)).toNat = 0x31)
    (h2 : (M (A + 2)).toNat = 0x3D) (hd : ∀ j, j < 4 → (M (A + 3 + j)).toNat = (bytes32 d).getD j 0) :
    bytesAt M A 7 = encode (.aluMR64 6 d 7) := by
  have := bytesAt_eq_of M A (encode (.aluMR64 6 d 7)) (by
    intro k hk
    have hl : (encode (.aluMR64 6 d 7)).length = 7 := rfl
    rw [hl] at hk
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (M (A + 0)).toNat = 0x48
      exact h0
    · change (M (A + 1)).toNat = 0x31
      exact h1
    · change (M (A + 2)).toNat = 0x3D
      exact h2
    · change (M (A + 3)).toNat = (bytes32 d).getD 0 0
      exact hd 0 (by omega)
    · change (M (A + 4)).toNat = (bytes32 d).getD 1 0
      have := hd 1 (by omega); rw [show A + 3 + 1 = A + 4 by omega] at this; exact this
    · change (M (A + 5)).toNat = (bytes32 d).getD 2 0
      have := hd 2 (by omega); rw [show A + 3 + 2 = A + 5 by omega] at this; exact this
    · change (M (A + 6)).toNat = (bytes32 d).getD 3 0
      have := hd 3 (by omega); rw [show A + 3 + 3 = A + 6 by omega] at this; exact this)
  exact this

theorem len_xorq (d : BitVec 32) : (encode (.aluMR64 6 d 7)).length = 7 := rfl

theorem rt_xorq (d : BitVec 32) (t : List Nat) : decodeL (encode (.aluMR64 6 d 7) ++ t) = some (.aluMR64 6 d 7, 7) :=
  rt_xorMR64 d t

theorem toNat_ofNat32_small (r : Nat) (h : r < 2 ^ 32) : (BitVec.ofNat 32 r).toNat = r := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem setWidth32_ofNat (r : Nat) : (BitVec.ofNat 64 r).setWidth 32 = BitVec.ofNat 32 r := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd]

theorem bytesAt_congr (M N : Mem) (A n : Nat) (h : ∀ k, k < n → M (A + k) = N (A + k)) :
    bytesAt M A n = bytesAt N A n := by
  apply List.ext_getElem
  · simp [bytesAt]
  · intro k h1 h2
    have hk : k < n := by simpa [bytesAt] using h1
    simp only [bytesAt, List.getElem_map, List.getElem_range]
    rw [h k hk]

/-- The triple, from the first `add dword` to the end of the `sub dword`. All hypotheses are about bytes of the current memory. -/
theorem patch3 (base o : Nat) (s : St) (z0 : Int) (r EA : Nat)
    (hrip : s.rip = base + o)
    (haddb : bytesAt s.mem (base + o) 6 = encode (.aluMR32 0 3 6))
    (hx0 : (s.mem (base + o + 6)).toNat = 0x48) (hx1 : (s.mem (base + o + 6 + 1)).toNat = 0x31)
    (hx2 : (s.mem (base + o + 6 + 2)).toNat = 0x3D)
    (hdisp : rd32 s.mem (base + o + 9) = sdisp z0)
    (hsubb : bytesAt s.mem (base + o + 13) 6 = encode (.aluMR32 5 (sdisp (-10)) 6))
    (hr6 : s.regs 6 = BitVec.ofNat 64 r) (hr : r < 2 ^ 31) (hz1 : -2 ^ 31 ≤ z0 + r) (hz2 : z0 + r < 2 ^ 31)
    (hea : (Int.ofNat (base + o + 13) + (z0 + r)).toNat = EA)
    (hdis : EA + 8 ≤ base + o + 9 ∨ base + o + 13 ≤ EA) (hdis2 : EA + 8 ≤ base + o + 13 ∨ base + o + 19 ≤ EA) :
    ∃ s3, run 3 s = some s3 ∧ s3.rip = base + o + 19 ∧ s3.mem = xorQword s.mem EA (s.regs 7) ∧
      (∀ i, s3.regs i = s.regs i) := by
  have hc : (BitVec.ofNat 64 r).setWidth 32 = BitVec.ofNat 32 r := setWidth32_ofNat r
  -- the add
  have d1 : decode s.mem s.rip = some (.aluMR32 0 3 6, 6) := by
    rw [hrip]
    exact decode_of s.mem _ _ _ 6 rfl (by omega) haddb (fun t => rt_addMR32 3 t)
  have st1 := step_of_decode s _ _ d1
  have a1 : ripEA s.rip 6 3 = base + o + 9 := by
    unfold ripEA
    have : (3 : BitVec 32).toInt = 3 := by decide
    rw [this, hrip]; simp only [Int.ofNat_eq_natCast]; omega
  have M1 := exec_aluMR32_mem 0 3 6 6 s (by decide)
  rw [a1] at M1
  have e1 : (aluW 0 (rd32 s.mem (base + o + 9)) ((s.regs 6).setWidth 32) s.fl.cf).1 =
      rd32 s.mem (base + o + 9) + BitVec.ofNat 32 r := by
    rw [hr6, hc]; rfl
  rw [e1, hdisp, sdisp_add] at M1
  have r1 : (exec (.aluMR32 0 3 6) 6 s).rip = s.rip + 6 := rfl
  have g1 : ∀ i, (exec (.aluMR32 0 3 6) 6 s).regs i = s.regs i := fun i => rfl
  generalize exec (.aluMR32 0 3 6) 6 s = s1 at M1 st1 r1 g1
  -- the xor qword, decoded from the modified displacement
  have hd' : (sdisp (z0 + r)).toInt = z0 + r := toInt_sdisp _ hz1 hz2
  have d2 : decode s1.mem s1.rip = some (.aluMR64 6 (sdisp (z0 + r)) 7, 7) := by
    rw [r1, hrip, M1]
    refine decode_of _ _ _ _ 7 (len_xorq _) (by omega) ?_ (fun t => rt_xorq _ t)
    apply bytesAt_xorq
    · rw [show base + o + 6 = base + o + 6 from rfl, wr32_outside _ _ _ _ (by omega)]; exact hx0
    · rw [wr32_outside _ _ _ _ (by omega)]; exact hx1
    · rw [wr32_outside _ _ _ _ (by omega)]; exact hx2
    · intro j hj
      rw [show base + o + 6 + 3 + j = (base + o + 9) + j by omega]
      exact wr32_bytes32 _ _ _ j hj
  have st2 := step_of_decode s1 _ _ d2
  have a2 : ripEA s1.rip 7 (sdisp (z0 + r)) = EA := by
    unfold ripEA
    rw [hd', r1, hrip, ← hea]
  have M2 := exec_aluMR64_mem 6 (sdisp (z0 + r)) 7 7 s1 (by decide)
  rw [a2] at M2
  have e2 : (aluW 6 (rd64 s1.mem EA) (s1.regs 7) s1.fl.cf).1 = rd64 s1.mem EA ^^^ s.regs 7 := by
    rw [g1]; rfl
  rw [e2, wr64_xor] at M2
  have r2 : (exec (.aluMR64 6 (sdisp (z0 + r)) 7) 7 s1).rip = s1.rip + 7 := rfl
  have g2 : ∀ i, (exec (.aluMR64 6 (sdisp (z0 + r)) 7) 7 s1).regs i = s1.regs i := fun i => rfl
  generalize exec (.aluMR64 6 (sdisp (z0 + r)) 7) 7 s1 = s2 at M2 st2 r2 g2
  -- the sub
  have d3 : decode s2.mem s2.rip = some (.aluMR32 5 (sdisp (-10)) 6, 6) := by
    have rr : s2.rip = base + o + 13 := by rw [r2, r1, hrip] <;> omega
    rw [rr]
    refine decode_of _ _ _ _ 6 rfl (by omega) ?_ (fun t => rt_subMR32 _ t)
    rw [← hsubb]
    apply bytesAt_congr
    intro k hk
    rw [M2, M1]
    unfold xorQword
    have h1 : ¬ (EA ≤ base + o + 13 + k ∧ base + o + 13 + k < EA + 8) := by omega
    rw [if_neg h1, wr32_outside _ _ _ _ (by omega)]
  have st3 := step_of_decode s2 _ _ d3
  have a3 : ripEA s2.rip 6 (sdisp (-10)) = base + o + 9 := by
    unfold ripEA
    have : (sdisp (-10)).toInt = -10 := toInt_sdisp _ (by omega) (by omega)
    rw [this, r2, r1, hrip]; simp only [Int.ofNat_eq_natCast]; omega
  have M3 := exec_aluMR32_mem 5 (sdisp (-10)) 6 6 s2 (by decide)
  rw [a3] at M3
  have g2' : s2.regs 6 = BitVec.ofNat 64 r := by rw [g2, g1, hr6]
  have e3 : (aluW 5 (rd32 s2.mem (base + o + 9)) ((s2.regs 6).setWidth 32) s2.fl.cf).1 =
      rd32 s2.mem (base + o + 9) - BitVec.ofNat 32 r := by
    rw [g2', hc]; rfl
  rw [e3] at M3
  have r3 : (exec (.aluMR32 5 (sdisp (-10)) 6) 6 s2).rip = s2.rip + 6 := rfl
  have g3 : ∀ i, (exec (.aluMR32 5 (sdisp (-10)) 6) 6 s2).regs i = s2.regs i := fun i => rfl
  generalize exec (.aluMR32 5 (sdisp (-10)) 6) 6 s2 = s3 at M3 st3 r3 g3
  refine ⟨s3, ?_, ?_, ?_, ?_⟩
  · rw [run_succ_some 2 s s1 st1, run_succ_some 1 s1 s2 st2, run_succ_some 0 s2 s3 st3]; rfl
  · rw [r3, r2, r1, hrip] <;> omega
  · rw [M3, M2, M1, ← sdisp_add, ← hdisp, ← wr64_xor]
    exact patch_mem s.mem (base + o + 9) EA (BitVec.ofNat 32 r) (s.regs 7) hdis
  · intro i; rw [g3, g2, g1]

end SmcTamper
