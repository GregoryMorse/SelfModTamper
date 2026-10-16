module
public import SmcTamper.Static.Iter

@[expose] public section

namespace SmcTamper

theorem kstate_ext_of (k' : KState) (m : Mem) (p : Nat) (su : BitVec 64) (a : k'.mem = m) (b : k'.ptr = p)
    (c : k'.sum = su) : (⟨m, p, su⟩ : KState) = k' := by
  cases k'; simp_all

theorem toNat_add8 (x : BitVec 64) (h : x.toNat + 8 < 2 ^ 63) : (x + 8).toNat = x.toNat + 8 := by
  rw [BitVec.toNat_add]
  have : (8 : BitVec 64).toNat = 8 := by decide
  rw [this]; omega

/-- Loop lemma: from the top of the loop with `n + 1` iterations remaining (`n` more after this one, determined by the
end pointer in RDI), the machine code reaches the exit address after `10 (n + 1)` steps having performed exactly
`staticRun (n + 1)` on the abstract kernel state. -/
theorem loop_run (a0 : Nat) (e : BitVec 64) (he : e.toNat + 8 < 2 ^ 63) :
    ∀ (n : Nat) (s : St), s.rip = a0 + 11 → CodeOk s.mem a0 → IsKernelOpcode (s.mem (a0 + 12)) →
      s.fl.cf = false → s.regs 7 = e → (s.regs 6).toNat + 8 * n < e.toNat →
      e.toNat ≤ (s.regs 6).toNat + 8 * (n + 1) →
      ∃ s', run (10 * (n + 1)) s = some s' ∧ s'.rip = a0 + 43 ∧ s'.regs 8 = s.regs 8 ∧
        s'.regs 3 = (staticRun (a0 + 12) (n + 1) ⟨s.mem, (s.regs 6).toNat, s.regs 3⟩).sum ∧
        s'.mem = (staticRun (a0 + 12) (n + 1) ⟨s.mem, (s.regs 6).toNat, s.regs 3⟩).mem ∧ CodeOk s'.mem a0 ∧
        trace (10 * (n + 1)) s = (List.replicate (n + 1) (iterRips a0)).flatten := by
  intro n
  induction n with
  | zero =>
    intro s hr hc hk hcf h7 hlt hge
    obtain ⟨s', hrun, hs, hm, h6, h7', h8, hjmp, hexit, htr⟩ :=
      iter_run a0 s hr hc hk hcf (by omega) (by rw [h7]; omega)
    have hb := toNat_add8 (s.regs 6) (by omega)
    refine ⟨s', by simpa using hrun, hexit ?_, h8, ?_, ?_, ?_, ?_⟩
    · rw [h6, hb, h7', h7]; omega
    · simpa [staticRun] using hs
    · simpa [staticRun] using hm
    · rw [hm]; unfold staticStep; dsimp only; exact codeOk_wr8 s.mem a0 _ hc
    · simpa using htr
  | succ n ih =>
    intro s hr hc hk hcf h7 hlt hge
    obtain ⟨s1, hrun, hs, hm, h6, h7', h8, hjmp, hexit, htr⟩ :=
      iter_run a0 s hr hc hk hcf (by omega) (by rw [h7]; omega)
    have hb := toNat_add8 (s.regs 6) (by omega)
    have hlt1 : (s1.regs 6).toNat < (s1.regs 7).toNat := by
      rw [h6, hb, h7', h7]; omega
    obtain ⟨hr1, hcf1⟩ := hjmp hlt1
    have hc1 : CodeOk s1.mem a0 := by
      rw [hm]; unfold staticStep; dsimp only; exact codeOk_wr8 s.mem a0 _ hc
    have hk1 : IsKernelOpcode (s1.mem (a0 + 12)) := by
      rw [hm]; unfold staticStep; dsimp only; simp only [wr8, if_true]
      exact kernelOpcode_xor_closed _ hk _
    obtain ⟨s', hrun', hr', h8', hs', hm', hc', htr'⟩ := ih s1 hr1 hc1 hk1 hcf1 (by rw [h7', h7]) (by rw [h6, hb]; omega)
      (by rw [h6, hb]; omega)
    have hk' := kstate_ext_of (staticStep (a0 + 12) ⟨s.mem, (s.regs 6).toNat, s.regs 3⟩) s1.mem
      ((s1.regs 6).toNat) (s1.regs 3) hm.symm (by rw [h6, hb]; rfl) hs.symm
    refine ⟨s', ?_, hr', by rw [h8', h8], ?_, ?_, hc', ?_⟩
    · have : 10 * (n + 1 + 1) = 10 + 10 * (n + 1) := by omega
      rw [this, run_add, hrun]; exact hrun'
    · rw [hs']; simp only [staticRun]; rw [hk']
    · rw [hm']; simp only [staticRun]; rw [hk']
    · have : 10 * (n + 1 + 1) = 10 + 10 * (n + 1) := by omega
      rw [this, trace_add 10 _ s s1 hrun, htr, htr']
      simp [List.replicate_succ]

end SmcTamper
