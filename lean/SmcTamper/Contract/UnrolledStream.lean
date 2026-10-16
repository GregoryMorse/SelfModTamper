module
public import SmcTamper.Spec.Contract
public import SmcTamper.Spec.Layout

@[expose] public section

namespace SmcTamper

/-! ## The executed-instruction stream of the unrolled kernel (steady state)

Per pass: `I` intro instructions (abstract: addresses inside the 92-byte intro, no stores modelled; the intro's and tail's
own stores are bounded separately in `UnrolledClears`), `148` units of eight instructions, the five padding `NOP`s,
`148` units, and the final `jmp L0`.  The stream is periodic with period `I + 2374`. The unit instructions are those of
`unitAt` (lengths 3,3,3,3,2,3,6,4); the seventh is the `XOR BYTE PTR [rip+d], DL` that stores into the opcode byte of unit
`(u + 148) mod 296`. -/

def slotOff : Nat → Nat
  | 0 => 0 | 1 => 3 | 2 => 6 | 3 => 9 | 4 => 12 | 5 => 14 | 6 => 17 | _ => 23

def slotLen : Nat → Nat
  | 0 => 3 | 1 => 3 | 2 => 3 | 3 => 3 | 4 => 2 | 5 => 3 | 6 => 6 | _ => 4

def unitEv (base u s : Nat) : Ev :=
  ⟨base + unitStart u + slotOff s, slotLen s, if s = 6 then some (base + opOff ((u + perPage) % numUnits), 1) else none⟩

def evR (base I r : Nat) : Ev :=
  if r < I then ⟨base + 3 + r % 92, 1, none⟩
  else if r - I < 1184 then unitEv base ((r - I) / 8) ((r - I) % 8)
  else if r - I < 1189 then ⟨base + 4091 + (r - I - 1184), 1, none⟩
  else if r - I < 2373 then unitEv base (148 + (r - I - 1189) / 8) ((r - I - 1189) % 8)
  else ⟨base + 8092, 5, none⟩

def periodOf (I : Nat) : Nat := I + 2374

def ulEv (base I t : Nat) : Ev := evR base I (t % periodOf I)

theorem unitStart_eq (k : Nat) : unitStart k = 95 + 27 * k + (if 148 ≤ k then 5 else 0) := by
  by_cases h : 148 ≤ k <;> simp [unitStart, rsiOf, introLen, unitLen, perPage, pageSize, nopPad, h] <;> omega

theorem slot_sum : slotOff 7 + slotLen 7 = 27 := rfl

/-- Shift of a residue by a bounded amount. -/
theorem mod_add_small (t k P : Nat) (hk : k < P) :
    (t + k) % P = if t % P + k < P then t % P + k else t % P + k - P := by
  have h1 : t = P * (t / P) + t % P := (Nat.div_add_mod t P).symm
  have h2 : t % P < P := Nat.mod_lt _ (by omega)
  have h3 : t + k = (t % P + k) + P * (t / P) := by omega
  rw [h3, Nat.add_mul_mod_self_left]
  by_cases h : t % P + k < P
  · rw [if_pos h, Nat.mod_eq_of_lt h]
  · rw [if_neg h]
    have : t % P + k - P < P := by omega
    rw [show t % P + k = (t % P + k - P) + P by omega, Nat.add_mod_right, Nat.mod_eq_of_lt this]
    omega

theorem granHit_one (a p l : Nat) : granHit 1 a 1 p l = true ↔ (a ≤ p + l - 1 ∧ p ≤ a) := by
  simp [granHit]

/-- At byte granularity, the only instruction slot covering the opcode byte of unit `v` is slot 0 of unit `v`. -/
theorem unit_hit (base w s v : Nat) (hw : w < 296) (hs : s < 8) (hv : v < 296)
    (h : granHit 1 (base + opOff v) 1 (base + unitStart w + slotOff s) (slotLen s) = true) : w = v ∧ s = 0 := by
  rw [granHit_one] at h
  have hu1 := unitStart_eq w
  have hu2 := unitStart_eq v
  simp only [opOff] at h
  obtain ⟨h1, h2⟩ := h
  by_cases c1 : 148 ≤ w <;> by_cases c2 : 148 ≤ v <;> simp only [c1, c2, if_true, if_false] at hu1 hu2 <;>
  (obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 := by omega) <;>
  simp only [slotOff, slotLen, and_true] at h1 h2 ⊢ <;> omega


set_option maxRecDepth 8000 in
/-- Event classification: the only event of the stream containing the opcode byte of unit `v` is the first instruction
of unit `v`, which sits at position `I + 8 v (+ 5 for page 2)` of the pass. -/
theorem evR_hit (base I r v : Nat) (hr : r < periodOf I) (hv : v < 296)
    (h : granHit 1 (base + opOff v) 1 (evR base I r).pc (evR base I r).len = true) :
    r = I + 8 * v + (if 148 ≤ v then 5 else 0) := by
  unfold periodOf at hr
  have hu2 := unitStart_eq v
  unfold evR at h
  by_cases c0 : r < I
  · simp only [c0, ite_true] at h
    rw [granHit_one] at h
    simp only [opOff] at h
    by_cases c2 : 148 ≤ v <;> simp only [c2, ite_true, ite_false] at hu2 <;> omega
  · simp only [c0, ite_false] at h
    by_cases c1 : r - I < 1184
    · simp only [c1, ite_true] at h
      have := unit_hit base ((r - I) / 8) ((r - I) % 8) v (by omega) (by omega) hv h
      by_cases c2 : 148 ≤ v <;> simp only [c2, ite_true, ite_false] <;> omega
    · simp only [c1, ite_false] at h
      by_cases c3 : r - I < 1189
      · simp only [c3, ite_true] at h
        rw [granHit_one] at h
        simp only [opOff] at h
        by_cases c2 : 148 ≤ v <;> simp only [c2, ite_true, ite_false] at hu2 <;> omega
      · simp only [c3, ite_false] at h
        by_cases c4 : r - I < 2373
        · simp only [c4, ite_true] at h
          have := unit_hit base (148 + (r - I - 1189) / 8) ((r - I - 1189) % 8) v (by omega) (by omega) hv h
          by_cases c2 : 148 ≤ v <;> simp only [c2, ite_true, ite_false] <;> omega
        · simp only [c4, ite_false] at h
          rw [granHit_one] at h
          simp only [opOff] at h
          by_cases c2 : 148 ≤ v <;> simp only [c2, ite_true, ite_false] at hu2 <;> omega

end SmcTamper
