module
public import SmcTamper.Unrolled.Main
public import SmcTamper.Layout.Compare

@[expose] public section

namespace SmcTamper

/-! ## R6 side facts: limits of the size assumptions, the termination-patch byte assumption, and C11 -/

/-- L04, first counterexample: when `size mod 2368 ∈ [1, 7]` the last pass has no whole unit, so the patch index
`finalUnits - 1` does not exist (the code patches unit `-1`). -/
theorem size_mod_small (size : Nat) (h1 : 1 ≤ size % 2368) (h2 : size % 2368 ≤ 7) (hs : 2368 ≤ size) :
    finalUnits size = 0 := by
  unfold finalUnits finalBytes passCount
  omega

/-- L04, second counterexample: when `8 ∤ size` the unrolled code reads `⌊size/8⌋` quadwords in the last pass,
while the C loop reads `⌈size/8⌉`. -/
theorem size_not_multiple : finalUnits 9 = 1 ∧ (9 + 7) / 8 = 2 := by decide

/-- The termination patch rewrites the five bytes `48 8D 49 08 48` at the LEA of the final unit.  The fifth is the
first byte of the *next* instruction.  In the dynamic image that byte is `48` for every unit except 147
(followed by the five-NOP padding, `90`) and 295 (followed by `JMP L0`, `E9`). -/
theorem next_byte_normal : ∀ k, k < 296 → k ≠ 147 → k ≠ 295 → dynAt (leaOff k + 4) = 0x48 := by
  decide +kernel

theorem next_byte_147 : dynAt (leaOff 147 + 4) = 0x90 := by decide +kernel

theorem next_byte_295 : dynAt (leaOff 295 + 4) = 0xE9 := by decide +kernel

end SmcTamper
