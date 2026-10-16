module
public import SmcTamper.X64.Decode

@[expose] public section

namespace SmcTamper

/-- The bytes of `TPComp` from `MOV RSI,RCX` to `MOV [R8],RBX` (the three `push` bytes before and `pop/ret` after are
outside the model). -/
def tpCompBytes : List Nat := (tpCompInstrs.map encode).flatten

/-- M-class: these are the bytes MASM emits (`ml64 /Fl` listing of `TP.asm`, offsets 0x03-0x30). -/
theorem tpCompBytes_listing :
    tpCompBytes =
      [0x48, 0x8B, 0xF1, 0x48, 0x8D, 0x3C, 0x16, 0x48, 0x33, 0xDB, 0xF8, 0x48, 0x13, 0x1E, 0x0F, 0x98, 0xC2,
       0x0F, 0x9A, 0xC0, 0xC0, 0xE0, 0x02, 0x0A, 0xD0, 0xC0, 0xE2, 0x03, 0x30, 0x15, 0xEA, 0xFF, 0xFF, 0xFF,
       0x48, 0x8D, 0x76, 0x08, 0x48, 0x3B, 0xFE, 0x7F, 0xE0, 0x49, 0x89, 0x18] := by decide

/-- Byte offset of the `k`-th instruction of a list. -/
def offsetOf (l : List Instr) (k : Nat) : Nat := ((l.take k).map (fun i => (encode i).length)).sum

/-- C20: in Fig. 2 the displacement `$-2-3-3-3-2-3` of `XOR BYTE PTR [...], DL` lands on the opcode byte of the ADC
(the byte after its REX prefix, `0xF` bytes into the function once the three pushes are counted), and that byte
holds the ADC opcode `0x13`. -/
theorem fig2_xor_targets_adc_opcode :
    tpCompInstrs[10]? = some (.xorMB (BitVec.ofInt 32 (-22)) 2) ∧
    ((offsetOf tpCompInstrs 10 + (encode (.xorMB (BitVec.ofInt 32 (-22)) 2)).length : Nat) : Int)
      + (BitVec.ofInt 32 (-22)).toInt = (offsetOf tpCompInstrs 4 + 1 : Nat) ∧
    tpCompBytes[offsetOf tpCompInstrs 4 + 1]? = some 0x13 ∧ 3 + (offsetOf tpCompInstrs 4 + 1) = 0xF := by
  decide

/-- C25: one unrolled unit is 27 bytes, and the `+1` of `byte_ptr(destlbl, 1)` (skip the REX byte) addresses the ADC
opcode of the target unit. -/
theorem unit_size_27 (d : BitVec 32) : (((unitInstrs d).map encode).flatten).length = 27 := by
  simp [unitInstrs, encode, List.flatten, bytes32]
  
theorem unit_adc_opcode_at_one (d : BitVec 32) : (((unitInstrs d).map encode).flatten)[1]? = some 0x13 := by
  simp [unitInstrs, encode, bytes32]

end SmcTamper
