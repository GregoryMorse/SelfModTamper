module
public import SmcTamper.Static.Loop

@[expose] public section

namespace SmcTamper

theorem toNat_ofNat_add (p q : Nat) (h : p + q < 2 ^ 64) :
    (BitVec.ofNat 64 p + BitVec.ofNat 64 q).toNat = p + q := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have : p % 2 ^ 64 = p := Nat.mod_eq_of_lt (by omega)
  have : q % 2 ^ 64 = q := Nat.mod_eq_of_lt (by omega)
  omega

/-- The control-flow trace of `TPComp` on `N = ⌈ulSize/8⌉` iterations: instruction addresses (offsets from
`MOV RSI,RCX`) executed in order, ending with the result store. It depends on `N` only. -/
def tpCompTrace (a0 N : Nat) : List Nat :=
  [a0, a0 + 3, a0 + 7, a0 + 10] ++ (List.replicate N (iterRips a0)).flatten ++ [a0 + 43]

/-- **Level 2 refines Level 1.** `TPComp` (the 46 bytes from `MOV RSI,RCX` to `MOV [R8],RBX`, with the `ADC` opcode byte
holding one of the four kernel opcodes) is run on the modelled ISA with `RCX = pData`, `RDX = ulSize`; it takes
`4 + 10 ⌈ulSize/8⌉ + 1` steps, ends after the final store, and the stored sum and the final memory are those of the
abstract static kernel `staticRun` on `⌈ulSize/8⌉` iterations. The only address hypothesis is `pData + ulSize + 8 < 2^63`
(so that the signed `JG` agrees with the unsigned address comparison, `jg_after_cmp`). -/
theorem tpcomp_run (a0 : Nat) (s0 : St) (p0 size : Nat) (hrip : s0.rip = a0) (hcode : CodeOk s0.mem a0)
    (hkop : IsKernelOpcode (s0.mem (a0 + 12))) (h1 : s0.regs 1 = BitVec.ofNat 64 p0)
    (h2 : s0.regs 2 = BitVec.ofNat 64 size) (hs : 1 ≤ size) (hb : p0 + size + 8 < 2 ^ 63) :
    ∃ s', run (4 + 10 * ((size + 7) / 8) + 1) s0 = some s' ∧ s'.rip = a0 + 46 ∧
      s'.regs 3 = (staticRun (a0 + 12) ((size + 7) / 8) ⟨s0.mem, p0, 0⟩).sum ∧
      s'.mem = wr64 (staticRun (a0 + 12) ((size + 7) / 8) ⟨s0.mem, p0, 0⟩).mem (s0.regs 8).toNat
        (staticRun (a0 + 12) ((size + 7) / 8) ⟨s0.mem, p0, 0⟩).sum ∧
      trace (4 + 10 * ((size + 7) / 8) + 1) s0 = tpCompTrace a0 ((size + 7) / 8) := by
  -- setup: MOV RSI,RCX; LEA RDI,[RSI+RDX]; XOR RBX,RBX; CLC
  obtain ⟨t4, e4, r4, m4, c4, q6, q7, q3, q8, tr4⟩ : ∃ t, run 4 s0 = some t ∧ t.rip = a0 + 11 ∧ t.mem = s0.mem ∧
      t.fl.cf = false ∧ t.regs 6 = s0.regs 1 ∧ t.regs 7 = s0.regs 1 + s0.regs 2 ∧ t.regs 3 = 0 ∧
      t.regs 8 = s0.regs 8 ∧ trace 4 s0 = [a0, a0 + 3, a0 + 7, a0 + 10] := by
    have d1 : decode s0.mem s0.rip = some (.movRR 6 1, 3) := by rw [hrip]; exact dec_movRR s0.mem a0 hcode
    obtain ⟨t1, ht1⟩ : ∃ t, t = exec (.movRR 6 1) 3 s0 := ⟨_, rfl⟩
    have s1 : step s0 = some t1 := by rw [ht1]; exact step_of_decode _ _ _ d1
    have r1 : t1.rip = a0 + 3 := by rw [ht1]; show s0.rip + 3 = _; rw [hrip]
    have m1 : t1.mem = s0.mem := by rw [ht1]; rfl
    have d2 : decode t1.mem t1.rip = some (.leaSib 7 6 2, 4) := by rw [m1, r1]; exact dec_leaSib s0.mem a0 hcode
    obtain ⟨t2, ht2⟩ : ∃ t, t = exec (.leaSib 7 6 2) 4 t1 := ⟨_, rfl⟩
    have s2 : step t1 = some t2 := by rw [ht2]; exact step_of_decode _ _ _ d2
    have r2 : t2.rip = a0 + 7 := by rw [ht2]; show t1.rip + 4 = _; rw [r1]
    have m2 : t2.mem = s0.mem := by rw [ht2]; exact m1
    have d3 : decode t2.mem t2.rip = some (.alu 6 3 3, 3) := by rw [m2, r2]; exact dec_xorRR s0.mem a0 hcode
    obtain ⟨t3, ht3⟩ : ∃ t, t = exec (.alu 6 3 3) 3 t2 := ⟨_, rfl⟩
    have s3 : step t2 = some t3 := by rw [ht3]; exact step_of_decode _ _ _ d3
    have r3 : t3.rip = a0 + 10 := by rw [ht3]; show t2.rip + 3 = _; rw [r2]
    have m3 : t3.mem = s0.mem := by rw [ht3]; exact m2
    have d4 : decode t3.mem t3.rip = some (.clc, 1) := by rw [m3, r3]; exact dec_clc s0.mem a0 hcode
    obtain ⟨t4, ht4⟩ : ∃ t, t = exec .clc 1 t3 := ⟨_, rfl⟩
    have s4 : step t3 = some t4 := by rw [ht4]; exact step_of_decode _ _ _ d4
    refine ⟨t4, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [run_succ_some 3 s0 t1 s1, run_succ_some 2 t1 t2 s2, run_succ_some 1 t2 t3 s3, run_succ_some 0 t3 t4 s4]; rfl
    · rw [ht4, exec_clc, r3]
    · rw [ht4, exec_clc, m3]
    · rw [ht4, exec_clc]
    · rw [ht4, exec_clc, ht3]; simp [exec, St.setReg, ht2, ht1]
    · rw [ht4, exec_clc, ht3]; simp [exec, St.setReg, ht2, ht1]
    · rw [ht4, exec_clc, ht3]; simp [exec, aluW, St.setReg, fin6]
    · rw [ht4, exec_clc, ht3]; simp [exec, aluW, St.setReg, ht2, ht1]
    · rw [trace_succ_some 3 s0 t1 s1, trace_succ_some 2 t1 t2 s2, trace_succ_some 1 t2 t3 s3,
        trace_succ_some 0 t3 t4 s4, hrip, r1, r2, r3]
      rfl
  -- the loop
  have hptr : (t4.regs 6).toNat = p0 := by
    rw [q6, h1, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hend : (t4.regs 7).toNat = p0 + size := by
    rw [q7, h1, h2]; exact toNat_ofNat_add p0 size (by omega)
  have hn : (size + 7) / 8 = ((size + 7) / 8 - 1) + 1 := by omega
  obtain ⟨s'', hrun, hr, h8, hs'', hm'', hc'', htr⟩ := loop_run a0 (t4.regs 7) (by omega) ((size + 7) / 8 - 1) t4 r4
    (by rw [m4]; exact hcode) (by rw [m4]; exact hkop) c4 rfl (by omega) (by omega)
  rw [m4, hptr, q3] at hs'' hm''
  rw [← hn] at hs'' hm''
  -- the result store
  have d5 : decode s''.mem s''.rip = some (.movStore 8 3, 3) := by
    rw [hr]; exact dec_store s''.mem a0 hc''
  have fin : step s'' = some (exec (.movStore 8 3) 3 s'') := step_of_decode _ _ _ d5
  refine ⟨exec (.movStore 8 3) 3 s'', ?_, ?_, ?_, ?_, ?_⟩
  · have : 4 + 10 * ((size + 7) / 8) + 1 = 4 + 10 * (((size + 7) / 8 - 1) + 1) + 1 := by omega
    rw [this, run_add, run_add, e4]
    show (run (10 * (((size + 7) / 8 - 1) + 1)) t4).bind (run 1) = _
    rw [hrun]
    show run 1 s'' = _
    rw [run_one, fin]
  · show s''.rip + 3 = _; rw [hr]
  · show s''.regs 3 = _
    rw [hs'']
  · show wr64 s''.mem (s''.regs 8).toNat (s''.regs 3) = _
    rw [hm'', hs'', h8, q8]

  · have hall : run (4 + 10 * ((size + 7) / 8)) s0 = some s'' := by
      rw [run_add, e4]
      show (run (10 * ((size + 7) / 8)) t4) = _
      rw [hn]; exact hrun
    rw [trace_add (4 + 10 * ((size + 7) / 8)) 1 s0 s'' hall, trace_add 4 (10 * ((size + 7) / 8)) s0 t4 e4,
      tr4, hn, htr, trace_succ_some 0 s'' _ fin, hr]
    simp [trace, tpCompTrace]

/-- **C21.** The operation number of the C loop stays in `{0, 1, 4, 5}` at every iteration, so the `default:` branch of
the `switch` (`res = 0`) is never taken when the initial opcode byte is one of the four kernel opcodes. -/
theorem cIter_isOp (m : Mem) (opAddr : Nat) : ∀ (n : Nat) (c : CState), IsOp c.op → IsOp (tpCompCIter m opAddr n c).op := by
  intro n
  induction n with
  | zero => intro c h; exact h
  | succ n ih =>
    intro c h
    apply ih
    show IsOp (cOpNext c.op _)
    rw [cOpNext_eq]
    exact isOp_xor_toggle _ h _

/-- **`static_emulation` (Fig. 2 ≡ Fig. 3 at the machine-code level).** Run the 46 bytes of `TPComp` on the modelled ISA
with `RCX = pData` (8-aligned), `RDX = ulSize ≥ 1`, `pData + ulSize + 8 < 2^63`, the `ADC` opcode byte equal to
`opcodeOf op0` for a kernel operation number `op0`. After `4 + 10 ⌈ulSize/8⌉ + 1` steps the program is at the end of the
function; `RBX` holds the sum computed by the C transcription `tpCompC`; the final operation number is again a kernel
one; and the memory is the initial one with the opcode byte replaced by `opcodeOf` of the C loop's final `op`, followed by
the 8-byte store of the sum at `R8`. No assumption is made on the contents of the data region, on where the opcode
byte lies relative to it, or on `R8` (the result store is applied last, to whatever memory results). -/
theorem static_emulation (a0 : Nat) (s0 : St) (p0 size op0 : Nat) (hrip : s0.rip = a0) (hcode : CodeOk s0.mem a0)
    (h0 : s0.mem (a0 + 12) = opcodeOf op0) (hop : IsOp op0) (h1 : s0.regs 1 = BitVec.ofNat 64 p0)
    (h2 : s0.regs 2 = BitVec.ofNat 64 size) (hs : 1 ≤ size) (hb : p0 + size + 8 < 2 ^ 63) (hal : p0 % 8 = 0) :
    ∃ s', run (4 + 10 * ((size + 7) / 8) + 1) s0 = some s' ∧ s'.rip = a0 + 46 ∧
      s'.regs 3 = (tpCompC s0.mem (a0 + 12) p0 size op0).1 ∧ IsOp (tpCompC s0.mem (a0 + 12) p0 size op0).2 ∧
      s'.mem = wr64 (wr8 s0.mem (a0 + 12) (opcodeOf (tpCompC s0.mem (a0 + 12) p0 size op0).2)) (s0.regs 8).toNat
        (tpCompC s0.mem (a0 + 12) p0 size op0).1 := by
  have hk : IsKernelOpcode (s0.mem (a0 + 12)) := (isKernelOpcode_iff _).2 ⟨op0, hop, h0.symm⟩
  obtain ⟨s', hrun, hr, hsum, hmem, _⟩ := tpcomp_run a0 s0 p0 size hrip hcode hk h1 h2 hs hb
  obtain ⟨e1, e2, e3⟩ := static_eq_c s0.mem (a0 + 12) p0 size op0 hk hop h0 hal
  refine ⟨s', hrun, hr, ?_, e2, ?_⟩
  · rw [hsum]; exact e1
  · rw [hmem, e3, e1]

/-- **C04 / P08 (control flow independent of data).** For any two initial states satisfying the hypotheses of
`static_emulation`, whatever their memory contents (data region, opcode byte), start pointers and result addresses, the
executed instruction addresses are identical: the trace depends on `⌈ulSize/8⌉` and the code address only. -/
theorem constant_flow (a0 : Nat) (size : Nat) (s0 s1 : St) (p0 p1 : Nat)
    (hs : 1 ≤ size) (hb0 : p0 + size + 8 < 2 ^ 63) (hb1 : p1 + size + 8 < 2 ^ 63)
    (hr0 : s0.rip = a0) (hr1 : s1.rip = a0) (hc0 : CodeOk s0.mem a0) (hc1 : CodeOk s1.mem a0)
    (hk0 : IsKernelOpcode (s0.mem (a0 + 12))) (hk1 : IsKernelOpcode (s1.mem (a0 + 12)))
    (h10 : s0.regs 1 = BitVec.ofNat 64 p0) (h11 : s1.regs 1 = BitVec.ofNat 64 p1)
    (h20 : s0.regs 2 = BitVec.ofNat 64 size) (h21 : s1.regs 2 = BitVec.ofNat 64 size) :
    trace (4 + 10 * ((size + 7) / 8) + 1) s0 = trace (4 + 10 * ((size + 7) / 8) + 1) s1 := by
  obtain ⟨_, _, _, _, _, t0⟩ := tpcomp_run a0 s0 p0 size hr0 hc0 hk0 h10 h20 hs hb0
  obtain ⟨_, _, _, _, _, t1⟩ := tpcomp_run a0 s1 p1 size hr1 hc1 hk1 h11 h21 hs hb1
  rw [t0, t1]

end SmcTamper
