module
public import SmcTamper.Unrolled.L2Tab
public import SmcTamper.Contract.UnrolledClears

@[expose] public section

namespace SmcTamper

/-! ## The intro's executed length in the steady state (gap G03)

A full pass of the Level-2 run (`pass_run`) executes `passLen = 3 + (8 * 296 + 5 + 1)` instructions: the three intro instructions
`sub rdi,2368`, `jg L1` (taken) and `clc`, the 296 units with the five padding `NOP`s, and the final `jmp L0`.  That is the period of the
contract stream `Contract/UnrolledStream` with `I = 3` and with the intro events `introEv`, which are the decoded instructions of the image. -/

theorem steps_full : steps 0 296 = 2373 := by decide +kernel

/-- The executed length of a pass is the period of the contract stream with `I = 3`. -/
theorem pass_len_is_period : passLen = periodOf 3 := by
  unfold passLen periodOf
  rw [steps_full]

/-- The three intro events are the decoded instructions at those addresses, and none of them stores. -/
theorem intro_stream_decode (enc : Instr → List Nat) (henc : EncOk enc) (base : Nat) (M : Mem)
    (hI : ImgOk enc base M (fun _ => False)) :
    decode M (introEv base 0).pc = some (.aluRI 5 7 2368, (introEv base 0).len) ∧
    decode M (introEv base 1).pc = some (.jcc 15 0x4C, (introEv base 1).len) ∧
    decode M (introEv base 2).pc = some (.clc, (introEv base 2).len) ∧
    (∀ r, (introEv base r).store = none) := by
  have dec := intro_dec enc henc base M (fun _ => False) hI (fun i _ _ h => h)
  refine ⟨dec (.aluRI 5 7 2368, 9, 7) (by decide), dec (.jcc 15 0x4C, 16, 2) (by decide), dec (.clc, 94, 1) (by decide),
    fun r => (introEv_facts base r).2.2.2⟩

/-- C24 with the real intro length: at byte granularity no unit store of the unrolled kernel causes a clear for any window of at
most `1181` instructions. -/
theorem pass_clears_byte_real (base W : Nat) (hW : W ≤ 1181) : passUnitClears 1 W base 3 = 0 :=
  pass_clears_byte base 3 W (by omega) (by omega)

end SmcTamper
