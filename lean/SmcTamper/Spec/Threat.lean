module
public import SmcTamper.Spec.Detection

@[expose] public section

namespace SmcTamper

/-! ## Threat model (statement level; plan D11)

**System.** A protected image `I0`, `n` checksum units, the protected addresses `prot`, the SMC opcode bytes `ops` (which vary
legitimately and are reset before each check), and the alarm policy parameter `k` (k consecutive timing failures of one unit).
Each unit has its region (`CheckUnit`), its own code and response code, a threshold `tau` and a native check time `native`.
The expected value of a unit is computed from `I0` by the Level-1 kernel.

**Executions.** An infinite stream of events.  The *world* holds a fetch view `F`, a data view `D` and a flag `split` that is
set once the views have been separated.  The protected program contributes `exec` and `check` events (its schedule); the adversary
contributes writes, view separation, physical (DMA) writes, register writes, and chooses the *path* of a check.

**Goal.** The adversary wins when a protected byte (other than an SMC opcode byte) is executed in modified form and no effective
alarm is ever raised.  Register tampering outside timed intervals and injected code that leaves covered bytes intact are outside
the goal (scope witnesses in R11c).

**Assumptions** (`Assumptions`) are structural properties of the system, the schedule and the adversary's events.  None mentions
`alarm` or `wins` (checked by `validation/threat_audit.py`). -/

/-! ### The kernel on two views -/

structure VState where
  F : Mem
  D : Mem
  ptr : Nat
  sum : BitVec 64

/-- One iteration of the static kernel with the opcode fetched from the fetch view `F` and data and writes on the data view
`D`; with `med` the adversary copies the written opcode byte into `F` (a *mediation*). -/
def vStep (opAddr : Nat) (med : Bool) (s : VState) : VState :=
  let opb := s.F opAddr
  let r := kAlu opb s.sum (rd64 s.D s.ptr)
  let nd := s.D opAddr ^^^ (BitVec.ofNat 8 (toggle r.1) <<< 3)
  { F := if med then wr8 s.F opAddr nd else s.F, D := wr8 s.D opAddr nd, ptr := s.ptr + 8, sum := r.2 }

def vRun (opAddr : Nat) (med : Nat → Bool) : Nat → Nat → VState → VState
  | _, 0, s => s
  | i, n + 1, s => vRun opAddr med (i + 1) n (vStep opAddr (med i) s)

/-- The value of a check on the views `F`, `D`: the unit resets its opcode byte (in the data view; in the fetch view too iff
the views are one image, `coh`), then runs. -/
def viewValue (cu : CheckUnit) (coh : Bool) (F D : Mem) (med : Nat → Bool) : BitVec 64 × BitVec 8 :=
  let D0 := wr8 D cu.opAddr cu.canon
  let F0 := if coh then D0 else F
  let s := vRun cu.opAddr med 0 (cu.size / 8) ⟨F0, D0, cu.start, 0⟩
  (s.sum, s.D cu.opAddr)

/-! ### System, cost contract, levels -/

structure CUnit where
  cu : CheckUnit
  code : Nat → Prop
  resp : Nat → Prop
  tau : Nat
  native : Nat

structure Sys where
  I0 : Mem
  n : Nat
  unit : Nat → CUnit
  prot : Nat → Prop
  ops : Nat → Prop
  k : Nat

def Sys.expected (S : Sys) (x : Nat) : BitVec 64 × BitVec 8 := (S.unit x).cu.value ((S.unit x).cu.reset S.I0)

def Sys.inRegion (S : Sys) (x a : Nat) : Prop :=
  (S.unit x).cu.start ≤ a ∧ a < (S.unit x).cu.start + 8 * ((S.unit x).cu.size / 8)

/-- Platform cost contract (D2): lower bounds on the elapsed time of the adversary's check paths. -/
structure Cost where
  emulLB : Nat → Nat
  kd : Nat
  km : Nat

inductive Level where
  | L0 | L1 | L2 | L3 | L4
  deriving DecidableEq

def Level.rank : Level → Nat
  | .L0 => 0 | .L1 => 1 | .L2 => 2 | .L3 => 3 | .L4 => 4

/-- Where the timing readings come from: the inline `RDTSC`/`RDTSCP` of the protected code, or an operating-system timer API. -/
inductive TimerSrc where
  | tsc | osApi
  deriving DecidableEq

/-- Capability (R-class, plan D11): hooking an OS timer API needs user mode; trapping or offsetting `RDTSC` needs ring 0
(`CR4.TSD`) or a hypervisor (RDTSC exiting, TSC offsetting). -/
def Level.forgesReading (l : Level) : TimerSrc → Prop
  | .osApi => 1 ≤ l.rank
  | .tsc => 2 ≤ l.rank

/-! ### Events and the world -/

inductive CheckPath where
  | honest
  | emulated
  | forged
  | neutral
  | mediated (med : Nat → Bool)

inductive TEv where
  | exec (a : Nat)
  | check (x : Nat) (p : CheckPath) (elapsed reading : Nat)
  | write (a : Nat) (b : BitVec 8)
  | splitWrite (a : Nat) (b : BitVec 8)
  | dmaWrite (a : Nat) (b : BitVec 8)
  | regWrite
  | idle

structure World where
  F : Mem
  D : Mem
  split : Bool

def World.init (S : Sys) : World := ⟨S.I0, S.I0, false⟩

def stepW (w : World) : TEv → World
  | .write a b => { w with F := wr8 w.F a b, D := wr8 w.D a b }
  | .splitWrite a b => { w with F := wr8 w.F a b, split := true }
  | .dmaWrite a b => { w with F := wr8 w.F a b, D := wr8 w.D a b }
  | _ => w

/-- The world before event `n` of the stream `tl`. -/
def worldAt (S : Sys) (tl : Nat → TEv) : Nat → World
  | 0 => World.init S
  | n + 1 => stepW (worldAt S tl n) (tl n)

/-- Whether a check on the world `w` along path `p` produces the expected value. -/
def checkOk (S : Sys) (w : World) (x : Nat) : CheckPath → Prop
  | .honest => viewValue (S.unit x).cu (!w.split) w.F w.D (fun _ => !w.split) = S.expected x
  | .emulated => True
  | .forged => True
  | .neutral => True
  | .mediated med => viewValue (S.unit x).cu false w.F w.D med = S.expected x

/-- What the cost contract admits for an event (platform facts, not security assumptions). -/
def Cost.admits (C : Cost) (S : Sys) : TEv → Prop
  | .check x .emulated e _ => C.emulLB x ≤ e
  | .check x .forged e _ => (S.unit x).native + C.kd ≤ e
  | .check x (.mediated med) e _ =>
      (S.unit x).native + C.km * ((List.range ((S.unit x).cu.size / 8)).countP med) ≤ e
  | .check x .honest e _ => e = (S.unit x).native
  | _ => True

/-- What each adversary level may emit.  A check event whose reading differs from the elapsed time needs the capability to
forge the timer in use. -/
def Level.allows (l : Level) (t : TimerSrc) (tl : Nat → TEv) (i : Nat) : TEv → Prop
  | .exec _ => True
  | .idle => True
  | .regWrite => 1 ≤ l.rank
  | .write _ _ => 1 ≤ l.rank ∨ (l = .L0 ∧ ∀ j, j < i → ∃ a b, tl j = .write a b)
  | .splitWrite _ _ => 2 ≤ l.rank
  | .dmaWrite _ _ => 4 ≤ l.rank
  | .check _ p e r =>
      (r = e ∨ l.forgesReading t) ∧
      (match p with
       | .honest => True
       | .emulated => 1 ≤ l.rank
       | .forged => 1 ≤ l.rank
       | .neutral => 1 ≤ l.rank
       | .mediated _ => 2 ≤ l.rank)

/-! ### Schedule, alarm, goal -/

/-- The check schedule: `ck x m` is the stream index of the `m`-th check of unit `x`. -/
structure Sched (n : Nat) (tl : Nat → TEv) where
  ck : Nat → Nat → Nat
  incr : ∀ x m, ck x m < ck x (m + 1)
  isChk : ∀ x m, x < n → ∃ p e r, tl (ck x m) = TEv.check x p e r
  complete : ∀ i x p e r, tl i = TEv.check x p e r → x < n → ∃ m, ck x m = i

/-- Event well-formedness: levels, the cost contract, and the meaning of the check paths. -/
structure WF (S : Sys) (C : Cost) (l : Level) (t : TimerSrc) (tl : Nat → TEv) : Prop where
  lvl : ∀ i, l.allows t tl i (tl i)
  cost : ∀ i, C.admits S (tl i)
  honestCode : ∀ i x e r, tl i = TEv.check x .honest e r →
    ∀ a, (S.unit x).code a → ¬ S.ops a → (worldAt S tl i).F a = S.I0 a
  neutralMod : ∀ i x e r, tl i = TEv.check x .neutral e r →
    ∃ a, (S.unit x).code a ∧ ¬ S.ops a ∧ (worldAt S tl i).F a ≠ S.I0 a
  medSplit : ∀ i x med e r, tl i = TEv.check x (.mediated med) e r → (worldAt S tl i).split = true

def timeFailAt (S : Sys) (tl : Nat → TEv) (c x : Nat) : Prop :=
  ∃ p e r, tl c = TEv.check x p e r ∧ (S.unit x).tau < r

def valueFailAt (S : Sys) (tl : Nat → TEv) (c x : Nat) : Prop :=
  ∃ p e r, tl c = TEv.check x p e r ∧ ¬ checkOk S (worldAt S tl c) x p

/-- A unit has a response mechanism and it is never modified (so its alarm takes effect): there is at least one response byte, and
every response byte keeps its original value. A unit without any response byte has nothing that could take effect. -/
def RespIntact (S : Sys) (tl : Nat → TEv) (x : Nat) : Prop :=
  (∃ a, (S.unit x).resp a) ∧ ∀ n a, (S.unit x).resp a → (worldAt S tl n).F a = S.I0 a

/-- An effective alarm: some unit with an intact response code sees a value mismatch, or a positive number `k` of consecutive
timing failures (with `k = 0` the timing branch would hold with no failed check at all, so it is excluded). -/
def Alarm (S : Sys) (tl : Nat → TEv) (sch : Sched S.n tl) : Prop :=
  ∃ x, x < S.n ∧ RespIntact S tl x ∧
    ((∃ m, valueFailAt S tl (sch.ck x m) x) ∨
      (0 < S.k ∧ ∃ s, ∀ j, j < S.k → timeFailAt S tl (sch.ck x (s + j)) x))

/-- Goal (a): a protected, non-opcode byte is executed while the fetch view differs from the original image. -/
def ExecViolation (S : Sys) (tl : Nat → TEv) : Prop :=
  ∃ j a, tl j = TEv.exec a ∧ S.prot a ∧ ¬ S.ops a ∧ (worldAt S tl j).F a ≠ S.I0 a

def Wins (S : Sys) (tl : Nat → TEv) (sch : Sched S.n tl) : Prop := ExecViolation S tl ∧ ¬ Alarm S tl sch

/-! ### Assumptions A1–A8 -/

/-- `x` covers `y`: `x`'s region contains all of `y`'s own code (other than opcode bytes). -/
def Covers (S : Sys) (x y : Nat) : Prop := ∀ a, (S.unit y).code a → ¬ S.ops a → S.inRegion x a

/-- Paths in the covers graph among the `n` units. -/
inductive Reach (S : Sys) : Nat → Nat → Prop where
  | refl {x : Nat} : x < S.n → Reach S x x
  | step {x y z : Nat} : Reach S x y → z < S.n → Covers S y z → Reach S x z

/-- Unit `x`'s own code (outside the opcode bytes) is modified by some write. -/
def ModWrite (S : Sys) (tl : Nat → TEv) (x : Nat) : Prop :=
  ∃ i a b, tl i = TEv.write a b ∧ (S.unit x).code a ∧ ¬ S.ops a ∧ b ≠ S.I0 a

def Intact (S : Sys) (tl : Nat → TEv) (x : Nat) : Prop := ¬ ModWrite S tl x

/-- A1 coherence: the fetch view and the data view are one image throughout. -/
def A1 (S : Sys) (tl : Nat → TEv) : Prop := ∀ n, (worldAt S tl n).split = false
/-- A2 coverage: every protected byte lies in some unit's region. -/
def A2cov (S : Sys) : Prop := ∀ a, S.prot a → ∃ x, x < S.n ∧ S.inRegion x a
/-- A2: every unit's code is protected. -/
def A2code (S : Sys) : Prop := ∀ x, x < S.n → ∀ a, (S.unit x).code a → S.prot a
/-- A2: the covers graph is strongly connected. -/
def A2conn (S : Sys) : Prop := ∀ x y, x < S.n → y < S.n → Reach S x y
/-- A2: at least one unit's code is never modified. -/
def A2intact (S : Sys) (tl : Nat → TEv) : Prop := ∃ v, v < S.n ∧ Intact S tl v
/-- A3 timing gap: native time ≤ threshold < emulation / debug-trap / mediation lower bound. -/
def A3 (S : Sys) (C : Cost) : Prop := ∀ x, x < S.n → (S.unit x).native ≤ (S.unit x).tau ∧ (S.unit x).tau < C.emulLB x ∧
    (S.unit x).tau < (S.unit x).native + C.kd ∧ (S.unit x).tau < (S.unit x).native + C.km
/-- A4: no writer outside the protected thread (DMA, other bus masters) acts. -/
def A4 (tl : Nat → TEv) : Prop := ∀ i a b, tl i ≠ TEv.dmaWrite a b
/-- A5 time integrity: every reading equals the elapsed time. -/
def A5 (tl : Nat → TEv) : Prop := ∀ i x p e r, tl i = TEv.check x p e r → r = e
/-- A6 persistence: the alarm count `k` is positive, and a modifying write persists through the next `k` scheduled checks of
every unit covering the byte. -/
def A6 (S : Sys) (tl : Nat → TEv) (sch : Sched S.n tl) : Prop :=
  0 < S.k ∧ ∀ i a b x m0, tl i = TEv.write a b → S.prot a → ¬ S.ops a → b ≠ S.I0 a → x < S.n → S.inRegion x a →
    i < sch.ck x m0 → (m0 = 0 ∨ sch.ck x (m0 - 1) ≤ i) →
    ∀ j, j < S.k → (worldAt S tl (sch.ck x (m0 + j))).D a ≠ S.I0 a
/-- A7 response coverage: each unit has a response code (at least one response byte), and all of it is part of the unit's own
(protected) code. -/
def A7 (S : Sys) : Prop := ∀ x, x < S.n → (∃ a, (S.unit x).resp a) ∧ ∀ a, (S.unit x).resp a → (S.unit x).code a ∧ ¬ S.ops a
/-- A8 non-compensation: whenever a modification lies in the region of an honestly running unit, its result differs. -/
def A8 (S : Sys) (tl : Nat → TEv) (sch : Sched S.n tl) : Prop :=
  ∀ x m e r, x < S.n → tl (sch.ck x m) = TEv.check x .honest e r →
    (∃ a, S.inRegion x a ∧ ¬ S.ops a ∧ (worldAt S tl (sch.ck x m)).D a ≠ S.I0 a) →
    ¬ checkOk S (worldAt S tl (sch.ck x m)) x .honest

structure Assumptions (S : Sys) (C : Cost) (tl : Nat → TEv) (sch : Sched S.n tl) : Prop where
  a1 : A1 S tl
  a2cov : A2cov S
  a2code : A2code S
  a2conn : A2conn S
  a2intact : A2intact S tl
  a3 : A3 S C
  a4 : A4 tl
  a5 : A5 tl
  a6 : A6 S tl sch
  a7 : A7 S
  a8 : A8 S tl sch

end SmcTamper
