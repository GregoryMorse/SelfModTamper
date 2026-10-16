module
public import SmcTamper.Unrolled.Main

@[expose] public section

namespace SmcTamper

/-! ## G02: reset of the unrolled kernel

The unit reset of the detection scheme rewrites every opcode byte with its canonical value. For the unrolled kernel these are the
296 bytes at `base + opOff u` (`opsMem base · ops0`). The proof is the Level-1 one: the run changes only those bytes (`unrolled_emulation`,
third component), so rewriting them restores the starting image. -/

theorem opsMem_opsMem (base : Nat) (m : Mem) (ops ops' : Nat → Nat) :
    opsMem base (opsMem base m ops') ops = opsMem base m ops := by
  funext a
  by_cases ha : ∃ u, u < numUnits ∧ a = base + opOff u
  · obtain ⟨u, hu, rfl⟩ := ha
    rw [opsMem_at base _ ops u hu, opsMem_at base m ops u hu]
  · have h1 : ∀ u, u < numUnits → a ≠ base + opOff u := fun u hu e => ha ⟨u, hu, e⟩
    rw [opsMem_other base _ ops a h1, opsMem_other base m ops a h1, opsMem_other base m ops' a h1]

/-- **Reset restores the canonical state (unrolled kernel).** After one call, rewriting the canonical opcode bytes gives back the
starting image (so a second call with reset starts from the same image). -/
theorem reset_restores_unrolled (base : Nat) (m : Mem) (ops0 : Nat → Nat) (p0 size : Nat)
    (hops : ∀ u, u < 296 → IsOp (ops0 u)) (hmem : ∀ u, u < 296 → m (base + opOff u) = opcodeOf (ops0 u))
    (hal : p0 % 8 = 0) (h8 : size % 8 = 0) (hpos : 8 ≤ size)
    (hno : ∀ i, i < finalUnits size → ∀ k j, k < 8 → j < 5 →
      p0 + 2368 * passCount size + 8 * i + k ≠ patchAddr base (finalUnits size) + j) :
    opsMem base (callUnrolled base size ⟨m, p0, 0⟩).mem ops0 = m := by
  obtain ⟨_, _, h3⟩ := unrolled_emulation base m ops0 p0 size hops hmem hal h8 hpos hno
  rw [h3, opsMem_opsMem]
  exact opsMem_self base m ops0 hmem

/-- The value of the second call (sum) is that of the first. -/
theorem reset_value_stable_unrolled (base : Nat) (m : Mem) (ops0 : Nat → Nat) (p0 size : Nat)
    (hops : ∀ u, u < 296 → IsOp (ops0 u)) (hmem : ∀ u, u < 296 → m (base + opOff u) = opcodeOf (ops0 u))
    (hal : p0 % 8 = 0) (h8 : size % 8 = 0) (hpos : 8 ≤ size)
    (hno : ∀ i, i < finalUnits size → ∀ k j, k < 8 → j < 5 →
      p0 + 2368 * passCount size + 8 * i + k ≠ patchAddr base (finalUnits size) + j) :
    (callUnrolled base size ⟨opsMem base (callUnrolled base size ⟨m, p0, 0⟩).mem ops0, p0, 0⟩).sum =
      (callUnrolled base size ⟨m, p0, 0⟩).sum := by
  rw [reset_restores_unrolled base m ops0 p0 size hops hmem hal h8 hpos hno]

end SmcTamper
