module
public import SmcTamper.Spec.ISA
public import SmcTamper.Spec.Layout

@[expose] public section

namespace SmcTamper

/-! ## Code images as instruction lists

`loopBody` is `TPCompLoop` / `gen_asm` from `MOV RDI,RDX` to `MOV [R8],RBX` (the three `push` bytes before and the three
`pop` bytes and `ret` after are outside the model). It is parametrised by nothing: every displacement is computed from
`Spec/Layout`. The AsmJit image uses `encodeA` for the register-register forms, the MASM image uses `encode`; both
decode to the same instruction list (`Layout/Compare`). -/

/-- The instructions of `TPComp` (Fig. 2 plus the setup and the result store; `push/pop/ret` are outside the model). -/
def tpCompInstrs : List Instr :=
  [.movRR 6 1, .leaSib 7 6 2, .alu 6 3 3, .clc, .aluM 2 3 6, .setcc 8 2, .setcc 10 0, .shlB 0 2, .orB 2 0,
   .shlB 2 3, .xorMB (BitVec.ofInt 32 (-22)) 2, .leaD 6 6 8, .alu 7 7 6, .jcc 15 0xE0, .movStore 8 3]

def sdisp (z : Int) : BitVec 32 := BitVec.ofInt 32 z

/-- Displacement of unit `u`'s `XOR BYTE PTR [rip+d], DL`: from the end of the `XOR` (unit offset 23) to the opcode byte of
unit `(u + 148) mod 296`. -/
def unitDisp (u : Nat) : BitVec 32 :=
  sdisp ((opOff ((u + perPage) % numUnits) : Int) - ((unitStart u + 23 : Nat) : Int))

/-- One unrolled unit (Fig. 4): `adc rbx,[rcx]; sets dl; setp al; shl al,2; or dl,al; shl dl,3; xor [rip+d],dl; lea rcx,[rcx+8]`. -/
def unitAt (u : Nat) : List Instr :=
  [.aluM 2 3 1, .setcc 8 2, .setcc 10 0, .shlB 0 2, .orB 2 0, .shlB 2 3, .xorMB (unitDisp u) 2, .leaD 1 1 8]

/-- The intro (after the three pushes), 92 bytes: unit count, page-2 correction, termination patch and its
self-modifying displacement. -/
def introBody : List Instr :=
  [.movRR 7 2, .alu 6 3 3, .aluRI 5 7 2368, .jcc 15 0x4C, .aluRI 0 7 2368, .shiftI 5 7 3, .dec 7, .imulI 6 7 27,
   .aluRI 7 7 148, .jcc 12 3, .aluRI8_32 0 6 5, .movI32 0 7974, .alu 5 0 6, .shiftI 4 0 8,
   .movI64 7 (BitVec.ofNat 64 0x4808498DA1), .alu 6 7 0, .aluMR32 0 3 6, .aluMR64 6 (sdisp 30) 7,
   .aluMR32 5 (sdisp (-10)) 6, .clc]

/-- The epilogue (up to and including the result store): `jmp L0`, the same patch applied to unit 0 and shifted by `ESI`
through the self-modified displacement, the restoring `sub`, and `mov [r8],rbx`. -/
def tailBody : List Instr :=
  [.jmp32 (sdisp (9 - 8097)), .aluMR32 0 3 6, .aluMR64 6 (sdisp ((leaOff 0 : Int) - 8110)) 7,
   .aluMR32 5 (sdisp (-10)) 6, .movStore 8 3]

def page1Units : List Instr := ((List.range perPage).map unitAt).flatten
def page2Units : List Instr := ((List.range perPage).map (fun i => unitAt (perPage + i))).flatten

/-- The whole loop body: intro, page 1, five `NOP`s, page 2, epilogue. -/
def loopBody : List Instr :=
  introBody ++ page1Units ++ List.replicate nopPad .nop ++ page2Units ++ tailBody

def pushes : List Nat := [0x53, 0x56, 0x57]
def pops : List Nat := [0x5F, 0x5E, 0x5B, 0xC3]

/-- Byte `i` (offset from the function start, `PUSH RBX`) of the loop image when instructions are encoded by `enc`:
`push×3`, intro, 148 units, 5 `NOP`s to the page boundary, 148 units, epilogue, `pop×3; ret`. Defined by region so that
each byte is found without unfolding the 296 units. -/
def loopAt (enc : Instr → List Nat) (i : Nat) : Nat :=
  let bytes (l : List Instr) : List Nat := (l.map enc).flatten
  if i < 3 then pushes.getD i 0
  else if i < introLen then (bytes introBody).getD (i - 3) 0
  else if i < introLen + perPage * unitLen then (bytes (unitAt ((i - introLen) / unitLen))).getD ((i - introLen) % unitLen) 0
  else if i < pageSize then 0x90
  else if i < pageSize + perPage * unitLen then
    (bytes (unitAt (perPage + (i - pageSize) / unitLen))).getD ((i - pageSize) % unitLen) 0
  else (bytes tailBody ++ pops).getD (i - (pageSize + perPage * unitLen)) 0

/-- Total length of the loop image in bytes. -/
def loopLen : Nat := pageSize + perPage * unitLen + ((tailBody.map encode).flatten ++ pops).length

/-- The dynamic kernel as AsmJit encodes it (`encodeA`), and the static `TPCompLoop` as MASM encodes it (`encode`). -/
def dynAt : Nat → Nat := loopAt encodeA
def staticAt : Nat → Nat := loopAt encode

/-- Machine code of `TPComp` (Fig. 2) including `push×3` and `pop×3; ret`. -/
def tpCompImage : List Nat := pushes ++ (tpCompInstrs.map encode).flatten ++ pops

end SmcTamper
