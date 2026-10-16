module
public import SmcTamper.Spec.Images

@[expose] public section

namespace SmcTamper

/-! ## The intro length measured with placeholders (L05)

`gen_asm` measures the intro with all three parameters equal to `MAXCHAR = 127` (`introbytes`, `code_size`, `max_page`)
and later emits it with `max_page = 148`, `introbytes = 95`, `code_size = 27`. Two immediates change size between the
two runs (`cmp rdi, max_page`: imm8 → imm32; `add esi, 4096 − max_page·code_size − introbytes`: imm32 → imm8) and the
changes cancel. The model below is AsmJit's observed policy: an ALU immediate is encoded as imm8 when it fits in a signed
byte, otherwise as imm32; `mov rax, imm` is the 7-byte `48 C7 C0 imm32` for the values that occur (observed in the dump of
`Layout/Compare`; with the 5-byte `B8 imm32` form the total would be 2 bytes shorter in both runs). Evidence about the
encoder, not a proof about AsmJit. -/

def immBytes (v : Int) : Nat := if -128 ≤ v ∧ v ≤ 127 then 1 else 4

/-- Size of the intro (including the three pushes) as a function of the three parameters. -/
def introSize (maxPage introBytes codeSize : Nat) (movRax : Nat) : Nat :=
  let rdiImm : Int := ((maxPage * 8 * 2 : Nat) : Int)
  let cmpImm : Int := (maxPage : Int)
  let addImm : Int := (4096 : Int) - (maxPage * codeSize : Nat) - introBytes
  3 + 3 + 3 + (3 + immBytes rdiImm) + 2 + (3 + immBytes rdiImm) + 4 + 3 + (3 + immBytes (codeSize : Int)) +
    (3 + immBytes cmpImm) + 2 + (2 + immBytes addImm) + movRax + 3 + 4 + 10 + 3 + 6 + 7 + 6 + 1

/-- The model reproduces the real intro: 95 bytes with the emitted parameters, equal to the length of the Lean image. -/
theorem intro_real : introSize 148 95 27 7 = 95 ∧ introSize 148 95 27 7 = pushes.length + ((introBody.map encode).flatten).length := by
  decide +kernel

/-- The placeholder measurement gives the same size: the `cmp` grows by 3 bytes, the `add` shrinks by 3. -/
theorem intro_measured : introSize 127 127 127 7 = 95 := by decide +kernel

/-- The cancellation does not depend on the `mov rax, imm` form as long as both runs use the same one. -/
theorem intro_cancellation (m : Nat) : introSize 127 127 127 m = introSize 148 95 27 m := by
  unfold introSize immBytes; simp

end SmcTamper
