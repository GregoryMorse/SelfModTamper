module
public import SmcTamper.Spec.Kernel

@[expose] public section

namespace SmcTamper

/-! ## Harvard and von Neumann machines (statement level)

A *Harvard machine* has a fixed control (type `C`, which includes any registers) and a data memory.
Each step reads exactly one data address, determined by the control, then moves to a new control and optionally writes
one data byte.  Its program is part of `C` and `next`/`write`; it is never fetched from the memory.

A *von Neumann machine* fetches its instruction window (`L` bytes at its program counter) from the same memory it writes,
reads `w` data bytes, and then executes. -/

structure Harvard (C : Type) where
  readAddr : C → Nat
  next : C → BitVec 8 → C
  write : C → BitVec 8 → Option (Nat × BitVec 8)

/-- Apply an optional write. -/
def applyWrite (m : Mem) : Option (Nat × BitVec 8) → Mem
  | none => m
  | some (a, v) => wr8 m a v

def Harvard.step {C : Type} (H : Harvard C) (c : C) (m : Mem) : C × Mem :=
  let b := m (H.readAddr c)
  (H.next c b, applyWrite m (H.write c b))

def Harvard.run {C : Type} (H : Harvard C) : Nat → C → Mem → C × Mem
  | 0, c, m => (c, m)
  | n + 1, c, m => H.run n (H.step c m).1 (H.step c m).2

/-- The data addresses read by the first `n` steps. -/
def Harvard.reads {C : Type} (H : Harvard C) : Nat → C → Mem → List Nat
  | 0, _, _ => []
  | n + 1, c, m => H.readAddr c :: H.reads n (H.step c m).1 (H.step c m).2

structure VonNeumann (S : Type) where
  L : Nat
  w : Nat
  pc : S → Nat
  dataAddr : S → (Fin L → BitVec 8) → Fin w → Nat
  exec : S → (Fin L → BitVec 8) → (Fin w → BitVec 8) → S × Option (Nat × BitVec 8)

/-- One von Neumann step: fetch `L` bytes at `pc`, read `w` data bytes, execute and write, all in one memory. -/
def VonNeumann.step {S : Type} (V : VonNeumann S) (s : S) (m : Mem) : S × Mem :=
  let win : Fin V.L → BitVec 8 := fun i => m (V.pc s + i.val)
  let dv : Fin V.w → BitVec 8 := fun j => m (V.dataAddr s win j)
  let r := V.exec s win dv
  (r.1, applyWrite m r.2)

/-- `H` simulates `V` (same observation): started from the embedding of any von Neumann state `s` on any memory `m`, `H`
reaches after `N` steps a control whose observation equals the observation of the state `V` reaches after one step. -/
def Simulates {C S Obs : Type} (H : Harvard C) (V : VonNeumann S) (emb : S → C) (N : Nat)
    (obsH : C → Obs) (obsV : S → Obs) : Prop :=
  ∀ (s : S) (m : Mem), obsH (H.run N (emb s) m).1 = obsV (V.step s m).1

/-- Byte `a` is *sensitive* for the step of `V` from `s` on `m`: some other value of that byte changes the observation. -/
def Sensitive {S Obs : Type} (V : VonNeumann S) (obsV : S → Obs) (s : S) (m : Mem) (a : Nat) : Prop :=
  ∃ v, obsV (V.step s (wr8 m a v)).1 ≠ obsV (V.step s m).1

/-! ### Split memory (the memory-splitting attack's view of the SMC kernel)

Instruction fetch reads the view `F`; data reads and every write use the view held in the state (`k.mem`).  The opcode
byte is *fetched*, so under splitting the kernel executes the opcode of `F`; the kernel's XOR into its opcode byte only
reaches the data view. -/

def splitStep (opAddr : Nat) (F : Mem) (k : KState) : KState :=
  let opb := F opAddr
  let r := kAlu opb k.sum (rd64 k.mem k.ptr)
  { mem := wr8 k.mem opAddr (k.mem opAddr ^^^ (BitVec.ofNat 8 (toggle r.1) <<< 3)), ptr := k.ptr + 8, sum := r.2 }

def splitRun (opAddr : Nat) (F : Mem) : Nat → KState → KState
  | 0, k => k
  | n + 1, k => splitRun opAddr F n (splitStep opAddr F k)

/-- A plain (non-SMC) checksum over the data view: the ALU function `op` is fixed by the checksum's own code, nothing is
fetched from the memory being checked. -/
def plainStep (op : BitVec 8) (k : KState) : KState :=
  { k with ptr := k.ptr + 8, sum := (kAlu op k.sum (rd64 k.mem k.ptr)).2 }

def plainRun (op : BitVec 8) : Nat → KState → KState
  | 0, k => k
  | n + 1, k => plainRun op n (plainStep op k)

end SmcTamper
