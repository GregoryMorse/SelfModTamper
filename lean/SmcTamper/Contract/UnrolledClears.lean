module
public import SmcTamper.Contract.UnrolledStream

@[expose] public section

namespace SmcTamper

theorem perPage_eq : perPage = 148 := by decide
theorem numUnits_eq : numUnits = 296 := by decide

/-- The stores of the stream are exactly the seventh instructions of the units. -/
theorem evR_store (base I r a w : Nat) (hr : r < periodOf I) (h : (evR base I r).store = some (a, w)) :
    ∃ u, u < 296 ∧ r = I + 8 * u + (if 148 ≤ u then 5 else 0) + 6 ∧ a = base + opOff ((u + 148) % 296) ∧ w = 1 := by
  unfold periodOf at hr
  unfold evR at h
  by_cases c0 : r < I
  · simp only [c0, ite_true] at h; cases h
  · simp only [c0, ite_false] at h
    by_cases c1 : r - I < 1184
    · simp only [c1, ite_true, unitEv] at h
      by_cases c6 : (r - I) % 8 = 6
      · simp only [c6, ite_true, Option.some.injEq, Prod.mk.injEq] at h
        refine ⟨(r - I) / 8, by omega, by rw [if_neg (by omega)]; omega, ?_, h.2.symm⟩
        rw [← h.1, perPage_eq, numUnits_eq]
      · simp only [c6, ite_false] at h; cases h
    · simp only [c1, ite_false] at h
      by_cases c3 : r - I < 1189
      · simp only [c3, ite_true] at h; cases h
      · simp only [c3, ite_false] at h
        by_cases c4 : r - I < 2373
        · simp only [c4, ite_true, unitEv] at h
          by_cases c6 : (r - I - 1189) % 8 = 6
          · simp only [c6, ite_true, Option.some.injEq, Prod.mk.injEq] at h
            refine ⟨148 + (r - I - 1189) / 8, by omega, by rw [if_pos (by omega)]; omega, ?_, h.2.symm⟩
            rw [← h.1, perPage_eq, numUnits_eq]
          · simp only [c6, ite_false] at h; cases h
        · simp only [c4, ite_false] at h; cases h

/-- **C24 (clears can disappear).**  At byte granularity (`g = 1`), with an intro of at least four executed instructions, no
unit store of the unrolled kernel causes a clear as long as the window is at most `1182` instructions: the nearest refetch of
a stored opcode byte is 1183 instructions later (148 units of eight instructions plus the five padding `NOP`s, less the
store's own position in its unit), and `I + 1179` instructions later for the stores of page 2 (through `jmp L0` and the intro). -/
theorem g1_no_unit_clear (base I W : Nat) (hI : 4 ≤ I) (hW : W ≤ 1182) (t : Nat) :
    streamClear 1 W (ulEv base I) t = false := by
  unfold streamClear
  cases hs : (ulEv base I t).store with
  | none => rfl
  | some p =>
    obtain ⟨a, w⟩ := p
    have hP : 0 < periodOf I := by unfold periodOf; omega
    have hr : t % periodOf I < periodOf I := Nat.mod_lt _ hP
    obtain ⟨u, hu, hru, hau, hw1⟩ := evR_store base I (t % periodOf I) a w hr hs
    simp only
    cases hany : (List.range W).any (fun d => granHit 1 a w (ulEv base I (t + 1 + d)).pc (ulEv base I (t + 1 + d)).len) with
    | false => rfl
    | true =>
      exfalso
      obtain ⟨d, hd, hhit⟩ := List.any_eq_true.mp hany
      rw [List.mem_range] at hd
      have hm := mod_add_small t (1 + d) (periodOf I) (by unfold periodOf; omega)
      have hr2 : (t + 1 + d) % periodOf I < periodOf I := Nat.mod_lt _ hP
      have hv : (u + 148) % 296 < 296 := Nat.mod_lt _ (by omega)
      unfold ulEv at hhit
      rw [hau, hw1] at hhit
      have := evR_hit base I ((t + 1 + d) % periodOf I) ((u + 148) % 296) hr2 hv hhit
      rw [show t + 1 + d = t + (1 + d) by omega, hm] at this
      unfold periodOf at *
      by_cases c1 : 148 ≤ u <;> by_cases c2 : 148 ≤ (u + 148) % 296 <;> simp only [c1, c2, ite_true, ite_false] at hru this <;>
      split at this <;> omega

theorem unitStart_range (k : Nat) (hk : k < 296) :
    (k < 148 → 95 ≤ unitStart k ∧ unitStart k + 27 ≤ 4091) ∧ (148 ≤ k → 4096 ≤ unitStart k ∧ unitStart k + 27 ≤ 8092) := by
  have := unitStart_eq k
  by_cases c : 148 ≤ k <;> simp only [c, ite_true, ite_false] at this <;> constructor <;> intro h <;> omega

set_option maxRecDepth 8000 in
/-- Page-granule classification of events (image at address 0): events before position `I + 1189` of the pass lie in the
image's first page, the later ones (units of page 2 and the final `jmp`) in the second. -/
theorem evR_pagehit0 (I r v : Nat) (hr : r < periodOf I) (hv : v < 296)
    (h : granHit 4096 (opOff v) 1 (evR 0 I r).pc (evR 0 I r).len = true) :
    (r < I + 1189 ∧ v < 148) ∨ (I + 1189 ≤ r ∧ 148 ≤ v) := by
  unfold periodOf at hr
  have hvs := unitStart_range v hv
  have hgh : (opOff v) / 4096 ≤ ((evR 0 I r).pc + (evR 0 I r).len - 1) / 4096 ∧
      (evR 0 I r).pc / 4096 ≤ (opOff v + 1 - 1) / 4096 := by
    simpa [granHit] using h
  obtain ⟨g1, g2⟩ := hgh
  simp only [opOff] at g1 g2
  unfold evR at g1 g2
  by_cases c0 : r < I
  · simp only [c0, ite_true] at g1 g2
    omega
  · simp only [c0, ite_false] at g1 g2
    by_cases c1 : r - I < 1184
    · simp only [c1, ite_true, unitEv] at g1 g2
      have hws := unitStart_range ((r - I) / 8) (by omega)
      (obtain h0 | h0 | h0 | h0 | h0 | h0 | h0 | h0 : (r - I) % 8 = 0 ∨ (r - I) % 8 = 1 ∨ (r - I) % 8 = 2 ∨ (r - I) % 8 = 3 ∨ (r - I) % 8 = 4 ∨ (r - I) % 8 = 5 ∨ (r - I) % 8 = 6 ∨ (r - I) % 8 = 7 := by omega) <;>
      simp only [h0, slotOff, slotLen] at g1 g2 <;> omega
    · simp only [c1, ite_false] at g1 g2
      by_cases c3 : r - I < 1189
      · simp only [c3, ite_true] at g1 g2
        omega
      · simp only [c3, ite_false] at g1 g2
        by_cases c4 : r - I < 2373
        · simp only [c4, ite_true, unitEv] at g1 g2
          have hws := unitStart_range (148 + (r - I - 1189) / 8) (by omega)
          (obtain h0 | h0 | h0 | h0 | h0 | h0 | h0 | h0 : (r - I - 1189) % 8 = 0 ∨ (r - I - 1189) % 8 = 1 ∨ (r - I - 1189) % 8 = 2 ∨ (r - I - 1189) % 8 = 3 ∨ (r - I - 1189) % 8 = 4 ∨ (r - I - 1189) % 8 = 5 ∨ (r - I - 1189) % 8 = 6 ∨ (r - I - 1189) % 8 = 7 := by omega) <;>
          simp only [h0, slotOff, slotLen] at g1 g2 <;> omega
        · simp only [c4, ite_false] at g1 g2
          omega

theorem evR_base (base I r : Nat) :
    (evR base I r).pc = base + (evR 0 I r).pc ∧ (evR base I r).len = (evR 0 I r).len := by
  unfold evR unitEv
  by_cases c0 : r < I
  · simp [c0]; omega
  · by_cases c1 : r - I < 1184
    · simp [c0, c1]; omega
    · by_cases c3 : r - I < 1189
      · simp [c0, c1, c3]; omega
      · by_cases c4 : r - I < 2373
        · simp [c0, c1, c3, c4]; omega
        · simp [c0, c1, c3, c4]

theorem granHit_shift (B a p l : Nat) (hl : 1 ≤ l) : granHit 4096 (4096 * B + a) 1 (4096 * B + p) l = granHit 4096 a 1 p l := by
  unfold granHit
  have e1 : (4096 * B + a) / 4096 = B + a / 4096 := by omega
  have e2 : (4096 * B + p + l - 1) / 4096 = B + (p + l - 1) / 4096 := by omega
  have e3 : (4096 * B + p) / 4096 = B + p / 4096 := by omega
  have e4 : (4096 * B + a + 1 - 1) / 4096 = B + (a + 1 - 1) / 4096 := by omega
  rw [e1, e2, e3, e4]
  simp only [decide_eq_decide]
  omega

theorem slotLen_pos (s : Nat) : 2 ≤ slotLen s := by
  unfold slotLen; split <;> omega

theorem evR_len_pos (I r : Nat) : 1 ≤ (evR 0 I r).len := by
  unfold evR unitEv
  by_cases c0 : r < I
  · simp [c0]
  · by_cases c1 : r - I < 1184
    · simp [c0, c1]; have := slotLen_pos ((r - I) % 8); omega
    · by_cases c3 : r - I < 1189
      · simp [c0, c1, c3]
      · by_cases c4 : r - I < 2373
        · simp [c0, c1, c3, c4]; have := slotLen_pos ((r - I - 1189) % 8); omega
        · simp [c0, c1, c3, c4]

theorem evR_pagehit (B I r v : Nat) (hr : r < periodOf I) (hv : v < 296)
    (h : granHit 4096 (4096 * B + opOff v) 1 (evR (4096 * B) I r).pc (evR (4096 * B) I r).len = true) :
    (r < I + 1189 ∧ v < 148) ∨ (I + 1189 ≤ r ∧ 148 ≤ v) := by
  obtain ⟨e1, e2⟩ := evR_base (4096 * B) I r
  have hl : 1 ≤ (evR 0 I r).len := evR_len_pos I r
  rw [e1, e2, granHit_shift _ _ _ _ hl] at h
  exact evR_pagehit0 I r v hr hv h

/-- Position, in the periodic stream, of the store of unit `u` (its seventh instruction). -/
def storePos (I u : Nat) : Nat := I + 8 * u + (if 148 ≤ u then 5 else 0) + 6

/-- Unit-store clears in one pass (the intro's and the tail's own stores are counted separately). -/
def passUnitClears (g W base I : Nat) : Nat :=
  (List.range numUnits).countP (fun u => streamClear g W (ulEv base I) (storePos I u))

theorem storePos_lt (I u : Nat) (hu : u < 296) : storePos I u < periodOf I := by
  unfold storePos periodOf; by_cases c : 148 ≤ u <;> simp only [c, ite_true, ite_false] <;> omega

theorem storePos_ev (base I u : Nat) (hu : u < 296) : ulEv base I (storePos I u) = unitEv base u 6 := by
  unfold ulEv
  rw [Nat.mod_eq_of_lt (storePos_lt I u hu)]
  unfold evR storePos
  by_cases c : 148 ≤ u
  · simp only [c, ite_true]
    have e1 : I + 8 * u + 5 + 6 - I = 8 * u + 11 := by omega
    rw [e1]
    have e2 : ¬ (I + 8 * u + 5 + 6 < I) := by omega
    have e3 : ¬ (8 * u + 11 < 1184) := by omega
    have e4 : ¬ (8 * u + 11 < 1189) := by omega
    have e5 : 8 * u + 11 < 2373 := by omega
    have e6 : (8 * u + 11 - 1189) / 8 = u - 148 := by omega
    have e7 : (8 * u + 11 - 1189) % 8 = 6 := by omega
    have e8 : 148 + (u - 148) = u := by omega
    simp only [e2, e3, e4, e5, ite_true, ite_false, e6, e7, e8]
  · simp only [c, ite_false]
    have e1 : I + 8 * u + 0 + 6 - I = 8 * u + 6 := by omega
    rw [e1]
    have e2 : ¬ (I + 8 * u + 0 + 6 < I) := by omega
    have e3 : 8 * u + 6 < 1184 := by omega
    have e6 : (8 * u + 6) / 8 = u := by omega
    have e7 : (8 * u + 6) % 8 = 6 := by omega
    simp only [e2, e3, ite_true, ite_false, e6, e7]

theorem page4096_clear (B I W u : Nat) (hW : W ≤ 2000) (hu : u < 296)
    (h : streamClear 4096 W (ulEv (4096 * B) I) (storePos I u) = true) :
    (u < 148 ∧ 1183 ≤ 8 * u + W) ∨ (148 ≤ u ∧ 2363 ≤ 8 * u + W) := by
  unfold streamClear at h
  rw [storePos_ev _ _ _ hu] at h
  simp only [unitEv, ite_true] at h
  obtain ⟨d, hd, hhit⟩ := List.any_eq_true.mp h
  rw [List.mem_range] at hd
  have hP : 0 < periodOf I := by unfold periodOf; omega
  have hm := mod_add_small (storePos I u) (1 + d) (periodOf I) (by unfold periodOf; omega)
  have hsp := storePos_lt I u hu
  have hr2 : (storePos I u + 1 + d) % periodOf I < periodOf I := Nat.mod_lt _ hP
  have hv : (u + perPage) % numUnits < 296 := by rw [numUnits_eq]; exact Nat.mod_lt _ (by omega)
  unfold ulEv at hhit
  have hpg := evR_pagehit B I ((storePos I u + 1 + d) % periodOf I) ((u + perPage) % numUnits) hr2 hv hhit
  rw [show storePos I u + 1 + d = storePos I u + (1 + d) by omega, hm, Nat.mod_eq_of_lt hsp] at hpg
  rw [perPage_eq, numUnits_eq] at hpg
  unfold storePos periodOf at *
  by_cases c1 : 148 ≤ u <;> simp only [c1, ite_true, ite_false, true_and, and_true] at hpg ⊢ <;> split at hpg <;> omega

theorem page_count_bound (W : Nat) (hW : W ≤ 2000) :
    (List.range 296).countP (fun u => decide ((u < 148 ∧ 1183 ≤ 8 * u + W) ∨ (148 ≤ u ∧ 2363 ≤ 8 * u + W))) ≤ 2 * ((W + 7) / 8) := by
  let lo1 := (1183 - W + 7) / 8
  let lo2 := max 148 ((2363 - W + 7) / 8)
  let L : List Nat := List.range' lo1 (148 - lo1) ++ List.range' lo2 (296 - lo2)
  have hnd : L.Nodup := by
    unfold L
    rw [List.nodup_append]
    refine ⟨List.nodup_range', List.nodup_range', ?_⟩
    intro x hx y hy hxy
    rw [List.mem_range'_1] at hx hy
    have : lo2 ≥ 148 := Nat.le_max_left _ _
    omega
  have hsub : ∀ u, u ∈ (List.range 296).filter (fun u => decide ((u < 148 ∧ 1183 ≤ 8 * u + W) ∨ (148 ≤ u ∧ 2363 ≤ 8 * u + W))) → u ∈ L := by
    intro u hu
    rw [List.mem_filter, List.mem_range, decide_eq_true_iff] at hu
    obtain ⟨h1, h2 | h2⟩ := hu
    · unfold L; rw [List.mem_append, List.mem_range'_1, List.mem_range'_1]; left; omega
    · have : lo2 ≥ 148 := Nat.le_max_left _ _
      unfold L; rw [List.mem_append, List.mem_range'_1, List.mem_range'_1]; right
      have : lo2 = max 148 ((2363 - W + 7) / 8) := rfl
      omega
  rw [List.countP_eq_length_filter]
  have h1 := List.Nodup.length_le_of_subset ((List.nodup_range).filter _) hsub
  have h2 : L.length = (148 - lo1) + (296 - lo2) := by unfold L; simp
  have h3 : lo2 = max 148 ((2363 - W + 7) / 8) := rfl
  have h4 : lo1 = (1183 - W + 7) / 8 := rfl
  omega

/-- **C13 (distinct pages reduce clears).**  With the image page-aligned and page granularity (`g = 4096`), the unit stores of
a pass cause at most `2 ⌈W/8⌉` clears: only the stores within `W` instructions of a page transition (the second page, and the
wrap through `jmp L0` to the intro in the first).  Compare `static_clears_ge`: about one clear per quadword, i.e. at least
`295` for the quadwords of one pass. -/
theorem pass_clears_page (B I W : Nat) (hW : W ≤ 2000) : passUnitClears 4096 W (4096 * B) I ≤ 2 * ((W + 7) / 8) := by
  refine Nat.le_trans ?_ (page_count_bound W hW)
  unfold passUnitClears
  apply List.countP_mono_left
  intro u hu h
  have hu' : u < 296 := by have := List.mem_range.mp hu; rw [numUnits_eq] at this; exact this
  exact decide_eq_true (page4096_clear B I W u hW hu' h)

/-- C24 for whole passes: at byte granularity no unit store clears (hence only the intro's and tail's own stores can). -/
theorem pass_clears_byte (base I W : Nat) (hI : 4 ≤ I) (hW : W ≤ 1182) : passUnitClears 1 W base I = 0 := by
  unfold passUnitClears
  rw [List.countP_eq_zero]
  intro u _
  simp [g1_no_unit_clear base I W hI hW]

end SmcTamper
