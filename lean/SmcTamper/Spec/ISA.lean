module
public import SmcTamper.Spec.Bits

@[expose] public section

namespace SmcTamper

/-! ## An x86-64 subset: instruction syntax and decoding

Only the instruction forms occurring in `TPComp`, `TPCompLoop` and the AsmJit-generated kernel are modelled; any
other byte sequence does not decode (the machine stops). Decoding reads the *current* memory (same-thread
self-modifying code is coherent, Intel SDM Vol. 3A "Handling Self- and Cross-Modifying Code"); the processor's
pipeline, caches and machine clears are not modelled here (they enter only through the platform contract).
The auxiliary flag AF is not modelled: no modelled instruction reads it. -/

/-- The five modelled status flags. -/
structure Flags where
  cf : Bool
  pf : Bool
  zf : Bool
  sf : Bool
  ovf : Bool
  deriving DecidableEq

/-- Instructions. Registers are numbered as in the encoding (`rax = 0, rcx = 1, rdx = 2, rbx = 3, rsp = 4,
rbp = 5, rsi = 6, rdi = 7, r8 = 8`). `f` is the 3-bit ALU function: `0 ADD, 1 OR, 2 ADC, 3 SBB, 4 AND, 5 SUB,
6 XOR, 7 CMP`. Memory operands are `[base]` (no displacement) or `[rip + disp32]`. -/
inductive Instr where
  | alu (f : Fin 8) (dst src : Fin 16)             -- REX.W (f*8+3) /r, register source
  | aluM (f : Fin 8) (dst base : Fin 16)           -- REX.W (f*8+3) /r, source `qword [base]`
  | movRR (dst src : Fin 16)                       -- REX.W 8B /r
  | movStore (base src : Fin 16)                   -- REX.W 89 /r, `mov qword [base], src`
  | aluRI (f : Fin 8) (r : Fin 16) (imm : BitVec 32)   -- REX.W 81 /f id (sign-extended)
  | aluRI8_32 (f : Fin 8) (r : Fin 16) (imm : BitVec 8) -- 83 /f ib on a 32-bit register (zero-extends)
  | shiftI (k : Fin 8) (r : Fin 16) (n : BitVec 8) -- REX.W C1 /k ib (k = 4 SHL, 5 SHR)
  | dec (r : Fin 16)                               -- REX.W FF /1
  | imulI (dst src : Fin 16) (imm : BitVec 8)      -- REX.W 6B /r ib
  | movI32 (r : Fin 16) (imm : BitVec 32)          -- REX.W C7 /0 id (sign-extended)
  | movI64 (r : Fin 16) (imm : BitVec 64)          -- REX.W B8+r io
  | leaD (dst base : Fin 16) (d : BitVec 8)        -- REX.W 8D /r, `[base + disp8]`
  | leaSib (dst base index : Fin 16)               -- REX.W 8D /r SIB, `[base + index]`
  | setcc (cc : Fin 16) (r : Fin 4)                -- 0F 90+cc /0 on AL, CL, DL, BL
  | shlB (r : Fin 4) (n : BitVec 8)                -- C0 /4 ib on AL, CL, DL, BL
  | orB (dst src : Fin 4)                          -- 0A /r on AL, CL, DL, BL
  | xorMB (disp : BitVec 32) (src : Fin 4)         -- 30 /r, `xor byte [rip + disp], src`
  | aluMR32 (f : Fin 8) (disp : BitVec 32) (src : Fin 16)  -- (f*8+1) /r, `op dword [rip + disp], src32`
  | aluMR64 (f : Fin 8) (disp : BitVec 32) (src : Fin 16)  -- REX.W (f*8+1) /r, `op qword [rip + disp], src`
  | clc
  | jcc (cc : Fin 16) (rel : BitVec 8)
  | jmp32 (rel : BitVec 32)
  | nop
  deriving DecidableEq

/-- Little-endian 32-bit value from four bytes (each below 256). -/
def le32 (a b c d : Nat) : BitVec 32 := BitVec.ofNat 32 (a + 256 * b + 65536 * c + 16777216 * d)

/-- Little-endian 64-bit value from eight bytes. -/
def le64 (a b c d e f g h : Nat) : BitVec 64 :=
  BitVec.ofNat 64 (a + 256 * (b + 256 * (c + 256 * (d + 256 * (e + 256 * (f + 256 * (g + 256 * h)))))))

/-- Decode a REX.W-prefixed instruction; `x` is the low three bits of the prefix (`R`, `X`, `B`). The returned length
excludes the prefix byte. -/
def decodeRexW (x : Nat) (r : List Nat) : Option (Instr × Nat) :=
  let hi (m : Nat) : Fin 16 := Fin.ofNat 16 (x / 4 % 2 * 8 + m / 8 % 8)
  let lo (m : Nat) : Fin 16 := Fin.ofNat 16 (x % 2 * 8 + m % 8)
  match r with
  | op :: m :: rest =>
    if op < 0x40 ∧ op % 8 = 3 ∧ m / 64 = 3 then some (.alu (Fin.ofNat 8 (op / 8)) (hi m) (lo m), 2)
    else if op < 0x40 ∧ op % 8 = 3 ∧ m / 64 = 0 ∧ m % 8 ≠ 4 ∧ m % 8 ≠ 5 then
      some (.aluM (Fin.ofNat 8 (op / 8)) (hi m) (lo m), 2)
    else if op = 0x8B ∧ m / 64 = 3 then some (.movRR (hi m) (lo m), 2)
    else if op = 0x89 ∧ m / 64 = 3 then some (.movRR (lo m) (hi m), 2)
    else if op < 0x40 ∧ op % 8 = 1 ∧ m / 64 = 3 then some (.alu (Fin.ofNat 8 (op / 8)) (lo m) (hi m), 2)
    else if op = 0x89 ∧ m / 64 = 0 ∧ m % 8 ≠ 4 ∧ m % 8 ≠ 5 then some (.movStore (lo m) (hi m), 2)
    else if op = 0x81 ∧ m / 64 = 3 then
      match rest with
      | a :: b :: c :: d :: _ => some (.aluRI (Fin.ofNat 8 (m / 8 % 8)) (lo m) (le32 a b c d), 6)
      | _ => none
    else if op = 0xC1 ∧ m / 64 = 3 ∧ (m / 8 % 8 = 4 ∨ m / 8 % 8 = 5) then
      match rest with
      | n :: _ => some (.shiftI (Fin.ofNat 8 (m / 8 % 8)) (lo m) (BitVec.ofNat 8 n), 3)
      | _ => none
    else if op = 0xFF ∧ m / 64 = 3 ∧ m / 8 % 8 = 1 then some (.dec (lo m), 2)
    else if op = 0x6B ∧ m / 64 = 3 then
      match rest with
      | i :: _ => some (.imulI (hi m) (lo m) (BitVec.ofNat 8 i), 3)
      | _ => none
    else if op = 0xC7 ∧ m / 64 = 3 ∧ m / 8 % 8 = 0 then
      match rest with
      | a :: b :: c :: d :: _ => some (.movI32 (lo m) (le32 a b c d), 6)
      | _ => none
    else if op = 0x8D ∧ m / 64 = 1 ∧ m % 8 ≠ 4 then
      match rest with
      | d :: _ => some (.leaD (hi m) (lo m) (BitVec.ofNat 8 d), 3)
      | _ => none
    else if op = 0x8D ∧ m / 64 = 0 ∧ m % 8 = 4 then
      match rest with
      | s :: _ =>
        if s / 64 = 0 ∧ x / 2 % 2 * 8 + s / 8 % 8 ≠ 4 then
          some (.leaSib (hi m) (Fin.ofNat 16 (x % 2 * 8 + s % 8)) (Fin.ofNat 16 (x / 2 % 2 * 8 + s / 8 % 8)), 3)
        else none
      | _ => none
    else if op < 0x40 ∧ op % 8 = 1 ∧ m / 64 = 0 ∧ m % 8 = 5 then
      match rest with
      | a :: b :: c :: d :: _ => some (.aluMR64 (Fin.ofNat 8 (op / 8)) (le32 a b c d) (hi m), 6)
      | _ => none
    else if 0xB8 ≤ op ∧ op ≤ 0xBF then
      match m :: rest with
      | a :: b :: c :: d :: e :: f :: g :: h :: _ =>
        some (.movI64 (Fin.ofNat 16 (x % 2 * 8 + (op - 0xB8))) (le64 a b c d e f g h), 9)
      | _ => none
    else none
  | _ => none

/-- Decode an instruction without a REX prefix. -/
def decodePlain (b0 : Nat) (r : List Nat) : Option (Instr × Nat) :=
  if b0 = 0xF8 then some (.clc, 1)
  else if b0 = 0x90 then some (.nop, 1)
  else if 0x70 ≤ b0 ∧ b0 ≤ 0x7F then
    match r with
    | d :: _ => some (.jcc (Fin.ofNat 16 (b0 - 0x70)) (BitVec.ofNat 8 d), 2)
    | _ => none
  else if b0 = 0xE9 then
    match r with
    | a :: b :: c :: d :: _ => some (.jmp32 (le32 a b c d), 5)
    | _ => none
  else if b0 = 0x0F then
    match r with
    | b1 :: m :: _ =>
      if 0x90 ≤ b1 ∧ b1 ≤ 0x9F ∧ m / 8 = 24 ∧ m % 8 < 4 then
        some (.setcc (Fin.ofNat 16 (b1 - 0x90)) (Fin.ofNat 4 (m % 8)), 3)
      else none
    | _ => none
  else if b0 = 0xC0 then
    match r with
    | m :: n :: _ =>
      if m / 8 = 28 ∧ m % 8 < 4 then some (.shlB (Fin.ofNat 4 (m % 8)) (BitVec.ofNat 8 n), 3) else none
    | _ => none
  else if b0 = 0x08 then
    match r with
    | m :: _ =>
      if m / 64 = 3 ∧ m / 8 % 8 < 4 ∧ m % 8 < 4 then
        some (.orB (Fin.ofNat 4 (m % 8)) (Fin.ofNat 4 (m / 8 % 8)), 2)
      else none
    | _ => none
  else if b0 = 0x0A then
    match r with
    | m :: _ =>
      if m / 64 = 3 ∧ m / 8 % 8 < 4 ∧ m % 8 < 4 then
        some (.orB (Fin.ofNat 4 (m / 8 % 8)) (Fin.ofNat 4 (m % 8)), 2)
      else none
    | _ => none
  else if b0 = 0x30 then
    match r with
    | m :: a :: b :: c :: d :: _ =>
      if m / 64 = 0 ∧ m % 8 = 5 ∧ m / 8 % 8 < 4 then some (.xorMB (le32 a b c d) (Fin.ofNat 4 (m / 8 % 8)), 6)
      else none
    | _ => none
  else if b0 = 0x83 then
    match r with
    | m :: i :: _ =>
      if m / 64 = 3 ∧ m % 8 < 8 then
        some (.aluRI8_32 (Fin.ofNat 8 (m / 8 % 8)) (Fin.ofNat 16 (m % 8)) (BitVec.ofNat 8 i), 3)
      else none
    | _ => none
  else if b0 < 0x40 ∧ b0 % 8 = 1 then
    match r with
    | m :: a :: b :: c :: d :: _ =>
      if m / 64 = 0 ∧ m % 8 = 5 then
        some (.aluMR32 (Fin.ofNat 8 (b0 / 8)) (le32 a b c d) (Fin.ofNat 16 (m / 8 % 8)), 6)
      else none
    | _ => none
  else none

/-- Decode one instruction from a list of byte values; returns the instruction and its length in bytes. -/
def decodeL : List Nat → Option (Instr × Nat)
  | [] => none
  | b0 :: r =>
    if 0x48 ≤ b0 ∧ b0 ≤ 0x4F then (decodeRexW (b0 - 0x48) r).map (fun p => (p.1, p.2 + 1))
    else decodePlain b0 r

/-- The `n` bytes starting at `a`, as natural numbers. -/
def bytesAt (m : Mem) (a n : Nat) : List Nat := (List.range n).map (fun k => (m (a + k)).toNat)

/-- Decode the instruction at address `a` of the *current* memory (at most 10 bytes are read). -/
def decode (m : Mem) (a : Nat) : Option (Instr × Nat) := decodeL (bytesAt m a 10)

def bytes32 (x : BitVec 32) : List Nat := [x.toNat % 256, x.toNat / 256 % 256, x.toNat / 65536 % 256, x.toNat / 16777216 % 256]
def bytes64 (x : BitVec 64) : List Nat :=
  (List.range 8).map (fun k => x.toNat / 256 ^ k % 256)
def modrm (md : Nat) (reg rm : Nat) : Nat := md * 64 + reg % 8 * 8 + rm % 8
def rexOf (reg rm : Nat) : Nat := 0x48 + 4 * (reg / 8) + rm / 8

/-- The canonical encoding of an instruction. -/
def encode : Instr → List Nat
  | .alu f d s => [rexOf d s, f.val * 8 + 3, modrm 3 d s]
  | .aluM f d b => [rexOf d b, f.val * 8 + 3, modrm 0 d b]
  | .movRR d s => [rexOf d s, 0x8B, modrm 3 d s]
  | .movStore b s => [rexOf s b, 0x89, modrm 0 s b]
  | .aluRI f r i => [rexOf 0 r, 0x81, modrm 3 f r] ++ bytes32 i
  | .aluRI8_32 f r i => [0x83, modrm 3 f r, i.toNat]
  | .shiftI k r n => [rexOf 0 r, 0xC1, modrm 3 k r, n.toNat]
  | .dec r => [rexOf 0 r, 0xFF, modrm 3 1 r]
  | .imulI d s i => [rexOf d s, 0x6B, modrm 3 d s, i.toNat]
  | .movI32 r i => [rexOf 0 r, 0xC7, modrm 3 0 r] ++ bytes32 i
  | .movI64 r i => [rexOf 0 r, 0xB8 + r.val % 8] ++ bytes64 i
  | .leaD d b x => [rexOf d b, 0x8D, modrm 1 d b, x.toNat]
  | .leaSib d b i => [0x48 + 4 * (d.val / 8) + 2 * (i.val / 8) + b.val / 8, 0x8D, modrm 0 d 4, modrm 0 i b]
  | .setcc cc r => [0x0F, 0x90 + cc.val, 0xC0 + r.val]
  | .shlB r n => [0xC0, 0xE0 + r.val, n.toNat]
  | .orB d s => [0x0A, modrm 3 d s]
  | .xorMB x s => [0x30, modrm 0 s 5] ++ bytes32 x
  | .aluMR32 f x s => [f.val * 8 + 1, modrm 0 s 5] ++ bytes32 x
  | .aluMR64 f x s => [rexOf s 0, f.val * 8 + 1, modrm 0 s 5] ++ bytes32 x
  | .clc => [0xF8]
  | .jcc cc r => [0x70 + cc.val, r.toNat]
  | .jmp32 r => [0xE9] ++ bytes32 r
  | .nop => [0x90]

/-- The register-register forms as AsmJit emits them (direction bit clear: `op r/m, r`); every other instruction is
encoded as in `encode`. The decoder accepts both directions (`decodeRexW`, `decodePlain`). -/
def encodeA : Instr → List Nat
  | .alu f d s => [rexOf s d, f.val * 8 + 1, modrm 3 s d]
  | .movRR d s => [rexOf s d, 0x89, modrm 3 s d]
  | .orB d s => [0x08, modrm 3 s d]
  | i => encode i

end SmcTamper
