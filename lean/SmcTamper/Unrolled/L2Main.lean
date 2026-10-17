module
public import SmcTamper.Unrolled.L2Fin2

@[expose] public section

namespace SmcTamper

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Level 2 of the unrolled kernel, part 13: the unrolled loop, as machine code, refines the abstract kernel -/

theorem run_trans (a b : Nat) (s t u : St) (h1 : run a s = some t) (h2 : run b t = some u) : run (a + b) s = some u := by
  rw [run_add, h1]; simpa using h2

/-- The page-2 correction of `rsi`: `cmp rdi,148; jl; add esi,5`. -/
theorem intro_mid (enc : Instr → List Nat) (henc : EncOk enc) (base : Nat) (s : St) (E : Nat → Prop) (w : Nat)
    (hw : w < 296) (hrip : s.rip = base + 36) (h7 : s.regs 7 = BitVec.ofNat 64 w)
    (h6 : s.regs 6 = BitVec.ofNat 64 (27 * w)) (hI : ImgOk enc base s.mem E) (hE : ∀ i, 3 ≤ i → i < 95 → ¬ E i) :
    ∃ m s', run m s = some s' ∧ s'.rip = base + 48 ∧ s'.mem = s.mem ∧ s'.regs 6 = BitVec.ofNat 64 (rsiOf w) ∧
      (∀ i : Fin 16, i.val ≠ 6 → s'.regs i = s.regs i) := by
  rcases Nat.lt_or_ge w 148 with h | h
  · obtain ⟨s', e, r, m, g⟩ := intro_mid_lt enc henc base s E w h hrip h7 h6 hI hE
    refine ⟨2, s', e, r, m, ?_, fun i _ => by rw [g]⟩
    rw [g, h6, rsiOf_eq, if_neg (by omega), Nat.add_zero]
  · obtain ⟨s', e, r, m, v6, g⟩ := intro_mid_ge enc henc base s E w h hw hrip h7 h6 hI hE
    refine ⟨3, s', e, r, m, ?_, g⟩
    rw [v6, rsiOf_eq, if_pos h]

theorem kernel_xor (base : Nat) (M : Mem) (w : Nat) (hw : w < 296)
    (hK : ∀ v, v < 296 → IsKernelOpcode (M (base + opOff v))) :
    ∀ v, v < 296 → IsKernelOpcode (xorQword M (base + leaOff w) (patchVal (w + 1)) (base + opOff v)) := by
  intro v hv
  rw [xorQword_apply M (base + leaOff w) (patchVal (w + 1)) (base + opOff v) (fun j hj e => ?_)]
  · exact hK v hv
  · by_cases h5 : 5 ≤ j
    · exact patchVal_high (w + 1) j h5 hj
    · exfalso
      have := patch_not_opcode (w + 1) v j (by omega) (by omega) hv (by omega)
      simp only [Nat.add_sub_cancel] at this
      omega

/-- The abstract state after the full passes and the termination patch. -/
def kq (base size : Nat) (k : KState) (w : Nat) : KState :=
  { fullPasses base (passCount size) k with
    mem := xorQword (fullPasses base (passCount size) k).mem (base + leaOff w) (patchVal (w + 1)) }

theorem callUnrolled_parts (base size : Nat) (k : KState) (w : Nat) (hn : finalUnits size = w + 1) :
    (callUnrolled base size k).sum = (unitsFrom base 0 (w + 1) (kq base size k w)).sum ∧
    (callUnrolled base size k).mem =
      xorQword (unitsFrom base 0 (w + 1) (kq base size k w)).mem (base + leaOff w) (patchVal (w + 1)) := by
  simp only [callUnrolled, kq, hn, patchAddr, Nat.add_sub_cancel]
  exact ⟨trivial, trivial⟩

/-- **Level 2 refinement of the unrolled kernel.** Started at the first instruction after the three pushes, with the data
pointer in `rcx`, the byte count in `rdx` and the result address in `r8`, the machine code runs to the instruction after the
store and leaves, in `rbx` and memory, what the abstract call computes. Conditions: the image sits at `base` (up to the
opcode bytes, which are kernel opcodes), the final pass has `n` units with `n ≠ 148, 296` (otherwise the five patched
bytes would run into the padding or the epilogue), at least one unit remains, and the pointers stay below `2^63`. -/
theorem unrolled_refines (enc : Instr → List Nat) (henc : EncOk enc) (base : Nat) (s : St) (p0 size : Nat)
    (hrip : s.rip = base + 3) (h1 : s.regs 1 = BitVec.ofNat 64 p0) (h2 : s.regs 2 = BitVec.ofNat 64 size)
    (hI : ImgOk enc base s.mem (fun _ => False)) (hK : ∀ v, v < 296 → IsKernelOpcode (s.mem (base + opOff v)))
    (hsz : 8 ≤ finalBytes size) (hn148 : finalUnits size ≠ 148) (hn296 : finalUnits size ≠ 296)
    (hb : p0 + size + 2368 < 2 ^ 63) :
    ∃ N s', run N s = some s' ∧ s'.rip = base + 8119 ∧
      s'.regs 3 = (callUnrolled base size ⟨s.mem, p0, 0⟩).sum ∧
      s'.mem = wr64 (callUnrolled base size ⟨s.mem, p0, 0⟩).mem (s.regs 8).toNat
        (callUnrolled base size ⟨s.mem, p0, 0⟩).sum := by
  have hfu : finalUnits size = finalBytes size / 8 := rfl
  have hq : 2368 * passCount size < size ∧ finalBytes size ≤ 2368 ∧ finalBytes size = size - 2368 * passCount size := by
    unfold finalBytes passCount at *; omega
  obtain ⟨w, hn⟩ : ∃ w, finalUnits size = w + 1 := ⟨finalUnits size - 1, by omega⟩
  have hw294 : w ≤ 294 := by omega
  have h147 : w ≠ 147 := by omega
  have hw296 : w < 296 := by omega
  -- the head and the full passes
  obtain ⟨sa, ea, ra, v7a, v3a, ma, ga⟩ := head_run enc henc base s size hrip h2 hI
  have hRa : Rel sa ⟨s.mem, p0, 0⟩ :=
    ⟨by show sa.mem = s.mem; exact ma, by show sa.regs 1 = BitVec.ofNat 64 p0; rw [ga 1 (by decide) (by decide)]; exact h1,
      by show sa.regs 3 = 0; exact v3a⟩
  have h7a : (sa.regs 7).toNat = size := by rw [v7a]; exact toNat_ofNat64_small size (by omega)
  obtain ⟨sb, eb, rb, v7b, Rb, gb, Ib, Kb⟩ := passes_run enc henc base (passCount size) sa ⟨s.mem, p0, 0⟩ ra
    (by omega) (by omega) hRa (by show p0 + 2368 * passCount size < 2 ^ 63; omega)
    (by rw [ma]; exact hI) (by rw [ma]; exact hK)
  have h7b : (sb.regs 7).toNat = finalBytes size := by rw [v7b, h7a]; omega
  -- the intro
  obtain ⟨sc, ec, rc, mc, v7c, v6c, gc⟩ := intro_pre enc henc base sb (fun _ => False) rb (by omega) (by omega) Ib
    (fun i _ _ h => h)
  have hdiv : (sb.regs 7).toNat / 8 - 1 = w := by rw [h7b]; omega
  rw [hdiv] at v7c v6c
  obtain ⟨m, sd, ed, rd, md, v6d, gd⟩ := intro_mid enc henc base sc (fun _ => False) w hw296 rc v7c v6c
    (by rw [mc]; exact Ib) (fun i _ _ h => h)
  have hIsd : ImgOk enc base sd.mem (fun _ => False) := by rw [md, mc]; exact Ib
  obtain ⟨se, ee, re, cfe, me, v7e, v6e, ge⟩ := intro_post enc henc base sd (fun _ => False) w hw296 rd v6d hIsd
    (fun i _ _ h => h)
  -- the units, the jump, the epilogue
  have hRe : Rel se (kq base size ⟨s.mem, p0, 0⟩ w) := by
    refine ⟨?_, ?_, ?_⟩
    · show se.mem = xorQword (fullPasses base (passCount size) ⟨s.mem, p0, 0⟩).mem (base + leaOff w) (patchVal (w + 1))
      rw [me, md, mc, Rb.mem]
    · show se.regs 1 = BitVec.ofNat 64 (fullPasses base (passCount size) ⟨s.mem, p0, 0⟩).ptr
      rw [ge 1 (by decide) (by decide), gd 1 (by decide), gc 1 (by decide) (by decide)]; exact Rb.ptr
    · show se.regs 3 = (fullPasses base (passCount size) ⟨s.mem, p0, 0⟩).sum
      rw [ge 3 (by decide) (by decide), gd 3 (by decide), gc 3 (by decide) (by decide)]; exact Rb.sum
  have hbq : (kq base size ⟨s.mem, p0, 0⟩ w).ptr + 8 * (w + 1) < 2 ^ 63 := by
    show (fullPasses base (passCount size) ⟨s.mem, p0, 0⟩).ptr + 8 * (w + 1) < 2 ^ 63
    rw [fullPasses_ptr]
    show p0 + 2368 * passCount size + 8 * (w + 1) < 2 ^ 63
    omega
  have hIe : ImgOk enc base se.mem (E0 w) := by
    rw [me]
    exact imgOk_mono enc base _ _ _ (imgOk_win enc base sd.mem (fun _ => False) (leaOff w) (patchVal (w + 1)) hIsd)
      (fun i h => by rcases h with h | h; exact False.elim h; exact h)
  have hKe : ∀ v, v < 296 → IsKernelOpcode (se.mem (base + opOff v)) := by
    rw [me]; exact kernel_xor base sd.mem w hw296 (by rw [md, mc]; exact Kb)
  have hjb : bytesAt se.mem (base + leaOff w) 5 = encode (.jmp32 (BitVec.ofNat 32 (patchImm - rsiOf w))) := by
    rw [me]
    exact patched_bytes sd.mem (base + leaOff w) w (lea_orig enc henc base sd.mem (fun _ => False) hIsd w hw294 h147
      (fun j _ h => h))
  obtain ⟨Nj, sj, ej, rj, sumj, memj, gj, Ij⟩ := patched_run enc henc base se (kq base size ⟨s.mem, p0, 0⟩ w) w hw294 h147
    re cfe hRe hbq hIe hKe hjb
  have h6j : sj.regs 6 = BitVec.ofNat 64 (rsiOf w) := by
    rw [gj 6 (by decide) (by decide) (by decide) (by decide), v6e, v6d]
  obtain ⟨Nf, sf, ef, rf, memf, gf⟩ := epilogue_run enc henc base sj w hw294 rj h6j Ij
  have h7j : sj.regs 7 = patchVal (w + 1) := by
    rw [gj 7 (by decide) (by decide) (by decide) (by decide), v7e]
  have h8j : sj.regs 8 = s.regs 8 := by
    rw [gj 8 (by decide) (by decide) (by decide) (by decide), ge 8 (by decide) (by decide), gd 8 (by decide),
      gc 8 (by decide) (by decide), gb 8 (by decide) (by decide) (by decide) (by decide) (by decide),
      ga 8 (by decide) (by decide)]
  obtain ⟨hcs, hcm⟩ := callUnrolled_parts base size ⟨s.mem, p0, 0⟩ w hn
  have hsnoc : unitsFrom base 0 (w + 1) (kq base size ⟨s.mem, p0, 0⟩ w) =
      unitStep base w (unitsFrom base 0 w (kq base size ⟨s.mem, p0, 0⟩ w)) := by
    rw [unitsFrom_snoc base w 0 _ (by rw [numUnits_296]; omega), Nat.zero_add, Nat.mod_eq_of_lt (by rw [numUnits_296]; omega)]
  refine ⟨2 + (passLen * passCount size + (6 + (m + (9 + (Nj + Nf))))), sf, ?_, rf, ?_, ?_⟩
  · refine run_trans _ _ _ _ _ ea (run_trans _ _ _ _ _ eb (run_trans _ _ _ _ _ ec (run_trans _ _ _ _ _ ed
      (run_trans _ _ _ _ _ ee (run_trans _ _ _ _ _ ej ef)))))
  · rw [gf 3, sumj, hcs, hsnoc]
  · rw [memf, h7j, h8j, sumj, memj, hcs, hcm, hsnoc]

end SmcTamper
