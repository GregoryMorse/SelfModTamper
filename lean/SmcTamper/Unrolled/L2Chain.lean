module
public import SmcTamper.Unrolled.L2Mem
public import SmcTamper.Static.Loop

@[expose] public section

namespace SmcTamper

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Level 2 of the unrolled kernel, part 4: units chained into passes

`pos w` is the offset at which unit `w` starts when counted past the five padding `NOP`s of page 1 (`pos 148 = 4096`,
`pos 296 = 8092`, the start of the epilogue). -/

def pos (w : Nat) : Nat := if w < 148 then 95 + 27 * w else 100 + 27 * w

theorem pos_spec (w : Nat) : (w < 148 → pos w = 95 + 27 * w) ∧ (148 ≤ w → pos w = 100 + 27 * w) := by
  unfold pos; split <;> omega

theorem unitStart_eq_pos (w : Nat) (hw : w < 296) : unitStart w = pos w := by
  have hp := perPage_148
  have hn := nopPad_5
  simp only [unitStart, rsiOf, pos, introLen, unitLen, hp, hn]
  split <;> split <;> omega

theorem opOff_ge (u : Nat) : 96 ≤ opOff u := by
  simp only [opOff, unitStart, introLen]; omega

theorem opOff_lt (u : Nat) (hu : u < 296) : opOff u + 1 ≤ 8092 := by
  have := unitStart_lt u hu
  simp only [opOff]; omega

/-- The coupling of the machine state to the abstract kernel state. -/
structure Rel (s : St) (k : KState) : Prop where
  mem : s.mem = k.mem
  ptr : s.regs 1 = BitVec.ofNat 64 k.ptr
  sum : s.regs 3 = k.sum

/-- Decoding an instruction of the loop image from memory. -/
theorem dec_img (enc : Instr → List Nat) (henc : EncOk enc) (base : Nat) (M : Mem) (E : Nat → Prop)
    (hI : ImgOk enc base M E) (i : Instr) (o n : Nat) (hn : (enc i).length = n) (hle : n ≤ 10) (hb : o + n ≤ loopLen)
    (hop : ∀ k, k < n → ∀ u, u < 296 → o + k ≠ opOff u) (hE : ∀ k, k < n → ¬ E (o + k))
    (hsl : ∀ k, k < n → loopAt enc (o + k) = (enc i).getD k 0)
    (hr : ∀ t, decodeL (enc i ++ t) = some (i, n)) : decode M (base + o) = some (i, n) := by
  subst hn
  apply decode_of M _ (enc i) i _ rfl hle
  · have hl : ∀ k, k < (enc i).length → (M (base + o + k)).toNat = (enc i).getD k 0 := by
      intro k hk
      rw [show base + o + k = base + (o + k) by omega, hI (o + k) (by omega) (hop k hk) (hE k hk), hsl k hk]
    exact bytesAt_eq_of M (base + o) (enc i) hl
  · exact hr

theorem loopAt_nop (enc : Instr → List Nat) (i : Nat) (h1 : 4091 ≤ i) (h2 : i < 4096) : loopAt enc i = 0x90 := by
  have hp := perPage_148
  unfold loopAt
  have c1 : ¬ i < 3 := by omega
  have c2 : ¬ i < introLen := by simp only [introLen]; omega
  have c3 : ¬ i < introLen + perPage * unitLen := by simp only [introLen, hp, unitLen]; omega
  have c4 : i < pageSize := by simp only [pageSize]; omega
  rw [if_neg c1, if_neg c2, if_neg c3, if_pos c4]

theorem dec_nop (enc : Instr → List Nat) (henc : EncOk enc) (base : Nat) (M : Mem) (E : Nat → Prop)
    (hI : ImgOk enc base M E) (i : Nat) (h1 : 4091 ≤ i) (h2 : i < 4096) (hE : ¬ E i) :
    decode M (base + i) = some (.nop, 1) := by
  have hop : ∀ u, u < 296 → i ≠ opOff u := by
    intro u hu e
    have hij : u < 148 ∨ 148 ≤ u := by omega
    have h3 := rsiOf_spec u
    have hp := perPage_148
    simp only [opOff, unitStart, introLen] at e
    omega
  have hb : loopAt enc i = 0x90 := loopAt_nop enc i h1 h2
  have hi := hI i (by rw [loopLen_8123]; omega) hop hE
  apply decode_of M _ [0x90] .nop 1 rfl (by omega)
  · exact bytesAt_eq_of M (base + i) [0x90] (fun k hk => by
      simp only [List.length_cons, List.length_nil] at hk
      have : k = 0 := by omega
      subst this
      simpa [hb] using hi)
  · intro t; rfl

theorem nops_run (enc : Instr → List Nat) (henc : EncOk enc) (base : Nat) (E : Nat → Prop) (c : Nat) :
    ∀ (s : St) (m : Nat), m + c = 5 → s.rip = base + 4091 + m → ImgOk enc base s.mem E →
      (∀ j, j < 5 → ¬ E (4091 + j)) → run c s = some { s with rip := s.rip + c } := by
  induction c with
  | zero => intro s m _ _ _ _; rfl
  | succ c ih =>
    intro s m hm hr hI hE
    have d : decode s.mem s.rip = some (.nop, 1) := by
      rw [show s.rip = base + (4091 + m) by omega]
      exact dec_nop enc henc base s.mem E hI (4091 + m) (by omega) (by omega) (hE m (by omega))
    have st : step s = some { s with rip := s.rip + 1 } := step_of_decode s _ _ d
    rw [run_succ_some c s _ st]
    have := ih { s with rip := s.rip + 1 } (m + 1) (by omega) (by simp only []; omega) hI hE
    rw [this]
    congr 2
    simp only [St.mk.injEq]
    omega

theorem imgOk_unit (enc : Instr → List Nat) (base : Nat) (M : Mem) (E : Nat → Prop) (hI : ImgOk enc base M E)
    (hK : ∀ v, v < 296 → IsKernelOpcode (M (base + opOff v))) (u : Nat) (k : KState) (hk : k.mem = M) :
    ImgOk enc base (unitStep base u k).mem E ∧
      ∀ v, v < 296 → IsKernelOpcode ((unitStep base u k).mem (base + opOff v)) := by
  have hn : numUnits = 296 := numUnits_296
  have ht : (u + perPage) % numUnits < 296 := by rw [hn]; omega
  have e : (unitStep base u k).mem = wr8 M (base + opOff ((u + perPage) % numUnits))
      (M (base + opOff ((u + perPage) % numUnits)) ^^^
        (BitVec.ofNat 8 (toggle (kAlu (M (base + opOff u)) k.sum (rd64 M k.ptr)).1) <<< 3)) := by
    unfold unitStep; dsimp only; rw [hk]
  rw [e]
  exact ⟨imgOk_wr8 enc base M E hI _ ht _, kernelOps_wr8 base M hK _ ht _⟩

/-- One unit (plus the five `NOP`s of page 1 after unit 147). -/
theorem unit_macro (enc : Instr → List Nat) (henc : EncOk enc) (base : Nat) (E : Nat → Prop) (s : St) (k : KState)
    (u : Nat) (hu : u < 296) (hrip : s.rip = base + unitStart u) (hcf : s.fl.cf = false) (hR : Rel s k)
    (hb : k.ptr + 8 < 2 ^ 64) (hI : ImgOk enc base s.mem E) (hE : ∀ o, o < 27 → ¬ E (unitStart u + o))
    (hEn : u = 147 → ∀ j, j < 5 → ¬ E (4091 + j)) (hK : ∀ v, v < 296 → IsKernelOpcode (s.mem (base + opOff v))) :
    ∃ s', run (8 + (if u = 147 then 5 else 0)) s = some s' ∧ s'.rip = base + pos (u + 1) ∧ s'.fl.cf = false ∧
      Rel s' (unitStep base u k) ∧
      (∀ i : Fin 16, i.val ≠ 0 → i.val ≠ 1 → i.val ≠ 2 → i.val ≠ 3 → s'.regs i = s.regs i) ∧
      ImgOk enc base s'.mem E ∧ (∀ v, v < 296 → IsKernelOpcode (s'.mem (base + opOff v))) := by
  have hptr : (s.regs 1).toNat = k.ptr := by
    rw [hR.ptr, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hk := kstate_ext_of k s.mem (s.regs 1).toNat (s.regs 3) hR.mem.symm hptr.symm hR.sum.symm
  obtain ⟨s7, e7, r7, c7, sum7, mem7, g7⟩ := unit7 enc henc base E s u hu hrip hcf hI (fun o ho => hE o (by omega)) hK
  rw [hk] at sum7 mem7
  have hI7 : ImgOk enc base s7.mem E ∧ ∀ v, v < 296 → IsKernelOpcode (s7.mem (base + opOff v)) := by
    rw [mem7]; exact imgOk_unit enc base s.mem E hI hK u k hR.mem.symm
  obtain ⟨s8, e8, r8, m8, f8, p8, g8⟩ := unit_lea enc henc base E s7 u hu (by rw [r7]) hI7.1
    (fun o h1 h2 => hE o h2)
  have hrel : Rel s8 (unitStep base u k) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [m8, mem7]
    · rw [p8, g7 1 (by decide) (by decide) (by decide), hR.ptr]
      show BitVec.ofNat 64 k.ptr + 8 = BitVec.ofNat 64 (k.ptr + 8)
      rw [BitVec.ofNat_add]; rfl
    · rw [g8 3 (by decide), sum7]
  have hI8 : ImgOk enc base s8.mem E ∧ ∀ v, v < 296 → IsKernelOpcode (s8.mem (base + opOff v)) := by
    rw [m8]; exact hI7
  have hcf8 : s8.fl.cf = false := by rw [f8]; exact c7
  have hrun8 : run 8 s = some s8 := by
    rw [show (8 : Nat) = 7 + 1 from rfl, run_add, e7]
    show run 1 s7 = _
    rw [run_one, e8]
  have hregs : ∀ i : Fin 16, i.val ≠ 0 → i.val ≠ 1 → i.val ≠ 2 → i.val ≠ 3 → s8.regs i = s.regs i := by
    intro i h0 h1 h2 h3
    have : i ≠ 1 := fun e => h1 (by rw [e]; rfl)
    rw [g8 i this, g7 i h0 h2 h3]
  by_cases h147 : u = 147
  · subst h147
    have p147 := pos_spec 147
    have p148 := pos_spec (147 + 1)
    have hu147 := unitStart_eq_pos 147 (by omega)
    have hn5 := nops_run enc henc base E 5 s8 0 rfl (by rw [r8]; omega) hI8.1 (hEn rfl)
    refine ⟨{ s8 with rip := s8.rip + 5 }, ?_, ?_, hcf8, ?_, ?_, ?_, ?_⟩
    · rw [show 8 + (if (147 : Nat) = 147 then 5 else 0) = 8 + 5 by simp, run_add, hrun8]
      exact hn5
    · show s8.rip + 5 = _
      rw [r8]; omega
    · exact ⟨hrel.mem, hrel.ptr, hrel.sum⟩
    · exact hregs
    · exact hI8.1
    · exact hI8.2
  · refine ⟨s8, ?_, ?_, hcf8, hrel, hregs, hI8.1, hI8.2⟩
    · rw [if_neg h147]; exact hrun8
    · have h1 := pos_spec u
      have h2 := pos_spec (u + 1)
      have h3 := unitStart_eq_pos u hu
      rw [r8]; omega

def steps (u j : Nat) : Nat := 8 * j + (if u ≤ 147 ∧ 147 < u + j then 5 else 0)

theorem steps_succ (u j : Nat) : steps u (j + 1) = (8 + (if u = 147 then 5 else 0)) + steps (u + 1) j := by
  unfold steps
  split <;> split <;> split <;> omega

theorem unitsFrom_succ_mod (base u j : Nat) (k : KState) (h : u + j + 1 ≤ 296) :
    unitsFrom base u (j + 1) k = unitsFrom base (u + 1) j (unitStep base u k) := by
  show unitsFrom base ((u + 1) % numUnits) j (unitStep base u k) = _
  rcases j with _ | j
  · rfl
  · rw [numUnits_296, Nat.mod_eq_of_lt (by omega)]

theorem units_chain (enc : Instr → List Nat) (henc : EncOk enc) (base : Nat) (E : Nat → Prop) :
    ∀ (j u : Nat) (s : St) (k : KState), u + j ≤ 296 → s.rip = base + pos u → s.fl.cf = false → Rel s k →
      k.ptr + 8 * j < 2 ^ 63 → ImgOk enc base s.mem E → (∀ v, v < 296 → IsKernelOpcode (s.mem (base + opOff v))) →
      (∀ i, 95 ≤ i → i < pos (u + j) → ¬ E i) →
      ∃ s', run (steps u j) s = some s' ∧ s'.rip = base + pos (u + j) ∧ s'.fl.cf = false ∧
        Rel s' (unitsFrom base u j k) ∧
        (∀ i : Fin 16, i.val ≠ 0 → i.val ≠ 1 → i.val ≠ 2 → i.val ≠ 3 → s'.regs i = s.regs i) ∧
        ImgOk enc base s'.mem E ∧ (∀ v, v < 296 → IsKernelOpcode (s'.mem (base + opOff v))) := by
  intro j
  induction j with
  | zero =>
    intro u s k hu hrip hcf hR hb hI hK hE
    refine ⟨s, ?_, by simpa using hrip, hcf, hR, fun _ _ _ _ _ => rfl, hI, hK⟩
    · have : steps u 0 = 0 := by unfold steps; split <;> omega
      rw [this]; rfl
  | succ j ih =>
    intro u s k hu hrip hcf hR hb hI hK hE
    have hu' : u < 296 := by omega
    have q1 := pos_spec u
    have q2 := pos_spec (u + 1)
    have q3 := pos_spec (u + (j + 1))
    have q4 := unitStart_eq_pos u hu'
    have q5 : 95 ≤ unitStart u := by simp only [unitStart, introLen]; omega
    have hE1 : ∀ o, o < 27 → ¬ E (unitStart u + o) := fun o ho => hE _ (by omega) (by omega)
    have hE2 : u = 147 → ∀ jj, jj < 5 → ¬ E (4091 + jj) := fun h jj hj => hE _ (by omega) (by subst h; omega)
    obtain ⟨s1, e1, r1, c1, R1, g1, I1, K1⟩ := unit_macro enc henc base E s k u hu' (by rw [hrip, q4])
      hcf hR (by omega) hI hE1 hE2 hK
    have hE3 : ∀ i, 95 ≤ i → i < pos (u + 1 + j) → ¬ E i := fun i h1 h2 =>
      hE i h1 (by rw [show u + (j + 1) = u + 1 + j by omega]; exact h2)
    have hb' : (unitStep base u k).ptr + 8 * j < 2 ^ 63 := by
      have : (unitStep base u k).ptr = k.ptr + 8 := rfl
      rw [this]; omega
    obtain ⟨s', e', r', c', R', g', I', K'⟩ := ih (u + 1) s1 (unitStep base u k) (by omega) r1 c1 R1 hb' I1 K1 hE3
    rw [show u + 1 + j = u + (j + 1) by omega] at r'
    rw [unitsFrom_succ_mod base u j k (by omega)]
    refine ⟨s', ?_, r', c', R', ?_, I', K'⟩
    · rw [steps_succ, run_add, e1]
      show run (steps (u + 1) j) s1 = _
      rw [e']
    · intro i h0 h1 h2 h3
      rw [g' i h0 h1 h2 h3, g1 i h0 h1 h2 h3]

end SmcTamper
