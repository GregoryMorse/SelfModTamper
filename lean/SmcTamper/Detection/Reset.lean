module
public import SmcTamper.Spec.Detection
public import SmcTamper.Bits.Bytes

@[expose] public section

namespace SmcTamper

/-! ## C44 (reset) and C05 (data stored in covered bytes) -/

/-- The kernel writes only its own opcode byte. -/
theorem staticRun_mem_other (opAddr : Nat) :
    ∀ (n : Nat) (k : KState) (x : Nat), x ≠ opAddr → (staticRun opAddr n k).mem x = k.mem x := by
  intro n
  induction n with
  | zero => intro k x _; rfl
  | succ n ih =>
    intro k x hx
    simp only [staticRun]
    rw [ih _ x hx]
    simp [staticStep, wr8, hx]

/-- With the reset, the starting memory depends only on the bytes other than the opcode byte. -/
theorem reset_ext (u : CheckUnit) (m1 m2 : Mem) (h : ∀ x, x ≠ u.opAddr → m1 x = m2 x) : u.reset m1 = u.reset m2 := by
  funext x
  unfold CheckUnit.reset wr8
  by_cases hx : x = u.opAddr
  · simp [hx]
  · simp [hx, h x hx]

/-- **Reset restores the canonical state.**  After a run, rewriting the opcode byte gives back the starting memory when it was
canonical, so a second call with reset behaves as the first. -/
theorem reset_restores (u : CheckUnit) (m : Mem) (hc : m u.opAddr = u.canon) : u.reset (u.run m).mem = m := by
  funext x
  unfold CheckUnit.reset wr8
  by_cases hx : x = u.opAddr
  · simp [hx, hc]
  · simp only [hx, if_false]
    exact staticRun_mem_other u.opAddr _ _ x hx

theorem reset_value_stable (u : CheckUnit) (m : Mem) (hc : m u.opAddr = u.canon) :
    u.value (u.reset (u.run m).mem) = u.value m := by
  rw [reset_restores u m hc]

/-- A unit with one qword `0x8000000000000000`: the kernel turns `ADC` into `CMP`. -/
def resetUnit : CheckUnit := ⟨64, 0, 8, 0x13⟩

def resetMem : Mem := fun a => if a = 64 then 0x13 else if a = 7 then 0x80 else 0

/-- **Without reset the state depends on the number of calls.**  The second call (starting from the first call's final opcode
state) has a different value from the first. -/
theorem no_reset_value_depends_on_calls : resetUnit.value (resetUnit.run resetMem).mem ≠ resetUnit.value resetMem := by
  decide +kernel

/-- With reset the second call has the first call's value. -/
theorem reset_value_same : resetUnit.value (resetUnit.reset (resetUnit.run resetMem).mem) = resetUnit.value resetMem :=
  reset_value_stable resetUnit resetMem (by decide)

/-! ### Frame: the value depends only on the covered bytes -/

theorem rd64_ext (m1 m2 : Mem) (a : Nat) (h : ∀ i, i < 8 → m1 (a + i) = m2 (a + i)) : rd64 m1 a = rd64 m2 a := by
  have h0 := h 0 (by decide); have h1 := h 1 (by decide); have h2 := h 2 (by decide); have h3 := h 3 (by decide)
  have h4 := h 4 (by decide); have h5 := h 5 (by decide); have h6 := h 6 (by decide); have h7 := h 7 (by decide)
  simp only [Nat.add_zero] at h0
  simp only [rd64, h0, h1, h2, h3, h4, h5, h6, h7]

theorem staticRun_frame (opAddr : Nat) :
    ∀ (n : Nat) (k1 k2 : KState), k1.ptr = k2.ptr → k1.sum = k2.sum →
      (∀ x, ((k1.ptr ≤ x ∧ x < k1.ptr + 8 * n) ∨ x = opAddr) → k1.mem x = k2.mem x) →
      (staticRun opAddr n k1).sum = (staticRun opAddr n k2).sum ∧
        (staticRun opAddr n k1).mem opAddr = (staticRun opAddr n k2).mem opAddr := by
  intro n
  induction n with
  | zero =>
    intro k1 k2 _ hs hm
    exact ⟨hs, hm opAddr (Or.inr rfl)⟩
  | succ n ih =>
    intro k1 k2 hp hs hm
    simp only [staticRun]
    have hop : k1.mem opAddr = k2.mem opAddr := hm opAddr (Or.inr rfl)
    have hrd : rd64 k1.mem k1.ptr = rd64 k2.mem k2.ptr := by
      rw [← hp]
      apply rd64_ext
      intro i hi
      exact hm _ (Or.inl ⟨by omega, by omega⟩)
    apply ih
    · simp [staticStep, hp]
    · simp [staticStep, hs, hop, hrd]
    · intro x hx
      simp only [staticStep, wr8]
      by_cases hxo : x = opAddr
      · subst hxo
        simp [hop, hs, hrd]
      · simp only [hxo, if_false]
        apply hm x
        rcases hx with ⟨h1, h2⟩ | h
        · left; simp only [staticStep] at h1 h2; omega
        · exact absurd h hxo

/-- **C05.**  The value of a run is determined by the covered bytes (the region and the opcode byte): data stored in covered
bytes is checked exactly like code. -/
theorem value_frame (u : CheckUnit) (m1 m2 : Mem)
    (h : ∀ x, ((u.start ≤ x ∧ x < u.start + 8 * (u.size / 8)) ∨ x = u.opAddr) → m1 x = m2 x) : u.value m1 = u.value m2 := by
  obtain ⟨h1, h2⟩ := staticRun_frame u.opAddr (u.size / 8) ⟨m1, u.start, 0⟩ ⟨m2, u.start, 0⟩ rfl rfl h
  unfold CheckUnit.value CheckUnit.run
  rw [h1, h2]

/-- A stored data byte inside the region is detected: changing byte `3` of a two-qword region changes the value. -/
def storeUnit : CheckUnit := ⟨64, 0, 16, 0x13⟩

def storeMem (b : BitVec 8) : Mem := fun a => if a = 64 then 0x13 else if a = 3 then b else if a = 9 then 1 else 0

theorem storage_tamper_detected : storeUnit.value (storeMem 0x55) ≠ storeUnit.value (storeMem 0x56) := by decide +kernel

end SmcTamper
