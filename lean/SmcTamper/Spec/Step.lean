module
public import SmcTamper.Spec.ISA

@[expose] public section

namespace SmcTamper

/-! ## Operational semantics of the subset

Flags that the Intel SDM leaves undefined after a shift or multiplication (OF after a multi-bit shift, SF/ZF/PF after
`imul`) are set to a fixed value here (`false` for OF, computed from the result for the others); no modelled
instruction reads such a flag before another instruction rewrites it (checked by the kernel proofs). -/

/-- Machine state: general registers, instruction pointer, status flags and byte memory. -/
structure St where
  regs : Fin 16 → BitVec 64
  rip : Nat
  fl : Flags
  mem : Mem

def St.setReg (s : St) (r : Fin 16) (v : BitVec 64) : St := { s with regs := fun i => if i = r then v else s.regs i }

/-- The low byte of register `r` (AL, CL, DL, BL for `r < 4`). -/
def St.low8 (s : St) (r : Fin 4) : BitVec 8 := (s.regs ⟨r.val, by omega⟩).setWidth 8

/-- Write the low byte, keeping the other 56 bits. -/
def St.setLow8 (s : St) (r : Fin 4) (v : BitVec 8) : St :=
  s.setReg ⟨r.val, by omega⟩ ((s.regs ⟨r.val, by omega⟩ &&& ~~~0xFF#64) ||| v.setWidth 64)

def rd32 (m : Mem) (a : Nat) : BitVec 32 :=
  (m a).setWidth 32 ||| ((m (a + 1)).setWidth 32 <<< 8) ||| ((m (a + 2)).setWidth 32 <<< 16) |||
  ((m (a + 3)).setWidth 32 <<< 24)

def wr32 (m : Mem) (a : Nat) (v : BitVec 32) : Mem :=
  wr8 (wr8 (wr8 (wr8 m a (v.setWidth 8)) (a + 1) ((v >>> 8).setWidth 8)) (a + 2) ((v >>> 16).setWidth 8))
    (a + 3) ((v >>> 24).setWidth 8)

def wr64 (m : Mem) (a : Nat) (v : BitVec 64) : Mem :=
  wr8 (wr8 (wr8 (wr8 (wr8 (wr8 (wr8 (wr8 m a (v.setWidth 8)) (a + 1) ((v >>> 8).setWidth 8)) (a + 2)
    ((v >>> 16).setWidth 8)) (a + 3) ((v >>> 24).setWidth 8)) (a + 4) ((v >>> 32).setWidth 8)) (a + 5)
    ((v >>> 40).setWidth 8)) (a + 6) ((v >>> 48).setWidth 8)) (a + 7) ((v >>> 56).setWidth 8)

/-- Result flags of a logical operation. -/
def logicFlags {w : Nat} (r : BitVec w) : Flags := ⟨false, pf r, decide (r = 0), sf r, false⟩

/-- The eight ALU functions on `w`-bit operands with carry-in `c`: result and the new flags. -/
def aluW {w : Nat} (f : Fin 8) (a b : BitVec w) (c : Bool) : BitVec w × Flags :=
  let cn : Nat := if c then 1 else 0
  match f.val with
  | 0 => let r := a + b
         (r, ⟨decide (2 ^ w ≤ a.toNat + b.toNat), pf r, decide (r = 0), sf r, a.msb == b.msb && r.msb != a.msb⟩)
  | 1 => let r := a ||| b; (r, logicFlags r)
  | 2 => let r := a + b + BitVec.ofNat w cn
         (r, ⟨decide (2 ^ w ≤ a.toNat + b.toNat + cn), pf r, decide (r = 0), sf r, a.msb == b.msb && r.msb != a.msb⟩)
  | 3 => let r := a - b - BitVec.ofNat w cn
         (r, ⟨decide (a.toNat < b.toNat + cn), pf r, decide (r = 0), sf r, a.msb != b.msb && r.msb != a.msb⟩)
  | 4 => let r := a &&& b; (r, logicFlags r)
  | 6 => let r := a ^^^ b; (r, logicFlags r)
  | _ => let r := a - b       -- 5 SUB and 7 CMP
         (r, ⟨decide (a.toNat < b.toNat), pf r, decide (r = 0), sf r, a.msb != b.msb && r.msb != a.msb⟩)

/-- Condition codes of `Jcc` / `SETcc` (SDM Vol. 2 condition-code table). -/
def cond (cc : Fin 16) (fl : Flags) : Bool :=
  match cc.val with
  | 0 => fl.ovf | 1 => !fl.ovf | 2 => fl.cf | 3 => !fl.cf | 4 => fl.zf | 5 => !fl.zf
  | 6 => fl.cf || fl.zf | 7 => !fl.cf && !fl.zf | 8 => fl.sf | 9 => !fl.sf | 10 => fl.pf | 11 => !fl.pf
  | 12 => fl.sf != fl.ovf | 13 => fl.sf == fl.ovf | 14 => fl.zf || (fl.sf != fl.ovf)
  | _ => !fl.zf && (fl.sf == fl.ovf)

/-- Address of a `[rip + disp32]` operand: the address of the next instruction plus the sign-extended displacement. -/
def ripEA (rip len : Nat) (disp : BitVec 32) : Nat := (Int.ofNat (rip + len) + disp.toInt).toNat

/-- Shift; flags: CF = last bit shifted out, others from the result (count 0 changes nothing). -/
def shiftW {w : Nat} (left : Bool) (a : BitVec w) (cnt : Nat) (old : Flags) : BitVec w × Flags :=
  if cnt = 0 then (a, old)
  else
    let r := if left then a <<< cnt else a >>> cnt
    let out := if left then a.getLsbD (w - cnt) else a.getLsbD (cnt - 1)
    (r, ⟨out, pf r, decide (r = 0), sf r, false⟩)

/-- Execute a decoded instruction of length `len` from state `s`. -/
def exec (i : Instr) (len : Nat) (s : St) : St :=
  let s' := { s with rip := s.rip + len }
  match i with
  | .alu f d r =>
    let p := aluW f (s.regs d) (s.regs r) s.fl.cf
    let s2 := { s' with fl := p.2 }
    if f = 7 then s2 else s2.setReg d p.1
  | .aluM f d b =>
    let p := aluW f (s.regs d) (rd64 s.mem (s.regs b).toNat) s.fl.cf
    let s2 := { s' with fl := p.2 }
    if f = 7 then s2 else s2.setReg d p.1
  | .movRR d r => s'.setReg d (s.regs r)
  | .movStore b r => { s' with mem := wr64 s.mem (s.regs b).toNat (s.regs r) }
  | .aluRI f r imm =>
    let p := aluW f (s.regs r) (imm.signExtend 64) s.fl.cf
    let s2 := { s' with fl := p.2 }
    if f = 7 then s2 else s2.setReg r p.1
  | .aluRI8_32 f r imm =>
    let p := aluW f ((s.regs r).setWidth 32) (imm.signExtend 32) s.fl.cf
    let s2 := { s' with fl := p.2 }
    if f = 7 then s2 else s2.setReg r (p.1.setWidth 64)
  | .shiftI k r n =>
    let p := shiftW (k.val = 4) (s.regs r) (n.toNat % 64) s.fl
    { s'.setReg r p.1 with fl := p.2 }
  | .dec r =>
    let a := s.regs r
    let res := a - 1
    { s'.setReg r res with fl := ⟨s.fl.cf, pf res, decide (res = 0), sf res, decide (a = BitVec.intMin 64)⟩ }
  | .imulI d r imm =>
    let full : Int := (s.regs r).toInt * imm.toInt
    let res : BitVec 64 := BitVec.ofInt 64 full
    { s'.setReg d res with fl := ⟨decide (res.toInt ≠ full), pf res, decide (res = 0), sf res, decide (res.toInt ≠ full)⟩ }
  | .movI32 r imm => s'.setReg r (imm.signExtend 64)
  | .movI64 r imm => s'.setReg r imm
  | .leaD d b x => s'.setReg d (s.regs b + x.signExtend 64)
  | .leaSib d b i => s'.setReg d (s.regs b + s.regs i)
  | .setcc cc r => s'.setLow8 r (if cond cc s.fl then 1 else 0)
  | .shlB r n =>
    let p := shiftW true (s.low8 r) (n.toNat % 32) s.fl
    { s'.setLow8 r p.1 with fl := p.2 }
  | .orB d r =>
    let res := s.low8 d ||| s.low8 r
    { s'.setLow8 d res with fl := logicFlags res }
  | .xorMB disp r =>
    let a := ripEA s.rip len disp
    let res := (s.mem a) ^^^ s.low8 r
    { s' with mem := wr8 s.mem a res, fl := logicFlags res }
  | .aluMR32 f disp r =>
    let a := ripEA s.rip len disp
    let p := aluW f (rd32 s.mem a) ((s.regs r).setWidth 32) s.fl.cf
    { s' with fl := p.2, mem := if f = 7 then s.mem else wr32 s.mem a p.1 }
  | .aluMR64 f disp r =>
    let a := ripEA s.rip len disp
    let p := aluW f (rd64 s.mem a) (s.regs r) s.fl.cf
    { s' with fl := p.2, mem := if f = 7 then s.mem else wr64 s.mem a p.1 }
  | .clc => { s' with fl := { s.fl with cf := false } }
  | .jcc cc rel =>
    if cond cc s.fl then { s with rip := (Int.ofNat (s.rip + len) + rel.toInt).toNat } else s'
  | .jmp32 rel => { s with rip := (Int.ofNat (s.rip + len) + rel.toInt).toNat }
  | .nop => s'

/-- One step: decode at `rip` in the current memory and execute; `none` if the bytes do not decode. -/
def step (s : St) : Option St :=
  match decode s.mem s.rip with
  | none => none
  | some (i, len) => some (exec i len s)

/-- `n` steps. -/
def run : Nat → St → Option St
  | 0, s => some s
  | n + 1, s => (step s).bind (run n)

end SmcTamper
