module
public import SmcTamper.Harvard.Interp
public import SmcTamper.Harvard.Separation

@[expose] public section

namespace SmcTamper

/-- A small memory: opcode byte `ADC` (0x13) at address 0, data qwords `0x8000000000000000` (bytes 8..15) and `5` (bytes 16..23). -/
def splitDemoMem : Mem := fun a => if a = 0 then 0x13 else if a = 15 then 0x80 else if a = 16 then 5 else 0

/-- **C06 (explicit witness).**  Under von Neumann execution the kernel's own XOR changes its opcode after the first
iteration (ADC to SBB) so the second iteration subtracts; under split memory the fetch view keeps ADC, so the checksums
of the same two data qwords differ. -/
theorem split_differs_from_vn :
    (splitRun 0 splitDemoMem 2 ⟨splitDemoMem, 8, 0⟩).sum ≠ (staticRun 0 2 ⟨splitDemoMem, 8, 0⟩).sum := by
  decide +kernel

/-- The fetch view of the splitting attack is unaffected by what the kernel writes: the split run's sum is the plain
checksum with the fixed operation of the fetch view whenever the opcode byte is the same operation each time, i.e. the
split sum depends on the opcode byte only through `F opAddr`. -/
theorem split_sum_fetch_only (opAddr : Nat) (F1 F2 : Mem) (h : F1 opAddr = F2 opAddr) (n : Nat) (k : KState) :
    splitRun opAddr F1 n k = splitRun opAddr F2 n k := by
  have : splitStep opAddr F1 = splitStep opAddr F2 := by
    funext k; simp [splitStep, h]
  induction n generalizing k with
  | zero => rfl
  | succ n ih => simp only [splitRun, this]; exact ih _

/-- The attack of assumption A1, concretely: the adversary patches the *executed* code (fetch view `F`, here the opcode
byte ADC replaced by SBB) and leaves the data view untouched.  A plain checksum (`plainRun`, which has no access to the
fetch view) cannot depend on that patch, whereas the SMC checksum of the same data differs. -/
theorem smc_detects_fetch_patch :
    (splitRun 0 (wr8 splitDemoMem 0 0x1B) 2 ⟨splitDemoMem, 8, 0⟩).sum ≠
      (splitRun 0 splitDemoMem 2 ⟨splitDemoMem, 8, 0⟩).sum := by
  decide +kernel

end SmcTamper
