module
public import SmcTamper.Spec.ISA
public import SmcTamper.Spec.Images

@[expose] public section

namespace SmcTamper

/-- Round trip of a 32-bit immediate through its four little-endian bytes. -/
theorem le32_bytes32 (x : BitVec 32) :
    le32 (x.toNat % 256) (x.toNat / 256 % 256) (x.toNat / 65536 % 256) (x.toNat / 16777216 % 256) = x := by
  apply BitVec.eq_of_toNat_eq
  have h := x.isLt
  simp only [le32, BitVec.toNat_ofNat]
  omega

/-- Trailing garbage after an instruction never influences its decoding. -/
def pad : List Nat := List.replicate 10 0xFF

/-- `i` decodes from its own encoding followed by arbitrary padding, with the right length. -/
abbrev RoundTrips (i : Instr) : Prop := decodeL (encode i ++ pad) = some (i, (encode i).length)

/-- One unrolled unit of the static/dynamic loop (the AsmJit snippet of Fig. 4) with displacement `d`. -/
def unitInstrs (d : BitVec 32) : List Instr :=
  [.aluM 2 3 1, .setcc 8 2, .setcc 10 0, .shlB 0 2, .orB 2 0, .shlB 2 3, .xorMB d 2, .leaD 1 1 8]

/-- The remaining forms of `TPCompLoop` (intro, termination patch, epilogue). -/
def loopInstrs (d : BitVec 32) : List Instr :=
  [.movRR 7 2, .alu 6 3 3, .aluRI 5 7 2368, .jcc 15 0x4C, .aluRI 0 7 2368, .shiftI 5 7 3, .dec 7, .imulI 6 7 27,
   .aluRI 7 7 148, .jcc 12 3, .aluRI8_32 0 6 5, .movI32 0 7974, .alu 5 0 6, .shiftI 4 0 8,
   .movI64 7 (le64 0xA1 0x8D 0x49 0x08 0x48 0 0 0), .alu 6 7 0, .aluMR32 0 d 6, .aluMR64 6 d 7, .aluMR32 5 d 6,
   .clc, .jmp32 d, .movStore 8 3]

/-- Every constructor instance used by the kernels round-trips, for displacement `0x12345678` (a representative
nonzero value; the general displacement case is `roundTrips_disp`). -/
theorem roundTrips_tpComp : ∀ i ∈ tpCompInstrs, RoundTrips i := by decide +kernel
theorem roundTrips_unit : ∀ i ∈ unitInstrs 0x12345678, RoundTrips i := by decide +kernel
theorem roundTrips_loop : ∀ i ∈ loopInstrs 0x12345678, RoundTrips i := by decide +kernel

theorem dec_xorMB (a b c e : Nat) : decodeL ([0x30, 0x15, a, b, c, e] ++ pad) = some (.xorMB (le32 a b c e) 2, 6) := rfl
theorem dec_addMR32 (a b c e : Nat) : decodeL ([0x01, 0x35, a, b, c, e] ++ pad) = some (.aluMR32 0 (le32 a b c e) 6, 6) := rfl
theorem dec_subMR32 (a b c e : Nat) : decodeL ([0x29, 0x35, a, b, c, e] ++ pad) = some (.aluMR32 5 (le32 a b c e) 6, 6) := rfl
theorem dec_xorMR64 (a b c e : Nat) :
    decodeL ([0x48, 0x31, 0x3D, a, b, c, e] ++ pad) = some (.aluMR64 6 (le32 a b c e) 7, 7) := rfl
theorem dec_jmp32 (a b c e : Nat) : decodeL ([0xE9, a, b, c, e] ++ pad) = some (.jmp32 (le32 a b c e), 5) := rfl

/-- The displacement-carrying forms round-trip for every displacement. -/
theorem roundTrips_disp (d : BitVec 32) :
    RoundTrips (.xorMB d 2) ∧ RoundTrips (.aluMR32 0 d 6) ∧ RoundTrips (.aluMR32 5 d 6) ∧
    RoundTrips (.aluMR64 6 d 7) ∧ RoundTrips (.jmp32 d) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := dec_xorMB (d.toNat % 256) (d.toNat / 256 % 256) (d.toNat / 65536 % 256) (d.toNat / 16777216 % 256)
    rw [le32_bytes32] at this; exact this
  · have := dec_addMR32 (d.toNat % 256) (d.toNat / 256 % 256) (d.toNat / 65536 % 256) (d.toNat / 16777216 % 256)
    rw [le32_bytes32] at this; exact this
  · have := dec_subMR32 (d.toNat % 256) (d.toNat / 256 % 256) (d.toNat / 65536 % 256) (d.toNat / 16777216 % 256)
    rw [le32_bytes32] at this; exact this
  · have := dec_xorMR64 (d.toNat % 256) (d.toNat / 256 % 256) (d.toNat / 65536 % 256) (d.toNat / 16777216 % 256)
    rw [le32_bytes32] at this; exact this
  · have := dec_jmp32 (d.toNat % 256) (d.toNat / 256 % 256) (d.toNat / 65536 % 256) (d.toNat / 16777216 % 256)
    rw [le32_bytes32] at this; exact this

end SmcTamper
