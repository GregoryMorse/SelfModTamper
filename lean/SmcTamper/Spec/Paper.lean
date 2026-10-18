module
public import SmcTamper.Spec.Threat
public import SmcTamper.Spec.Harvard

@[expose] public section

namespace SmcTamper.Paper

/-! ## The statement (Palomar Challenge surface)

Scope, as in `lean/THREAT_MODEL.md`: an abstract model of SMC checksumming units against an adversary at levels `L0`..`L4`, with the
assumptions `A1`..`A8` (structural conditions on the timeline, never "the attacker is detected") and the cost contract `Cost`
(mediation and emulation have a lower bound). Nothing here says anything about real hardware: platform behaviour enters only as the
fields of `Cost`, `Level.allows` and the well-formedness structure `WF`. -/

/-- T1 (security). For every well-formed timeline (levels, cost contract, check paths) of a system that satisfies A1-A8: if a
protected byte outside the SMC opcode bytes `ops` is ever executed while the fetch view differs from the original image at that
byte (`ExecViolation`), then an effective alarm (`Alarm`) occurs somewhere in the infinite timeline, not necessarily before that
execution. The SMC opcode bytes legitimately vary, so executing one in a changed state is outside the goal. -/
def SecurityTheorem : Prop :=
  ∀ (S : Sys) (C : Cost) (l : Level) (t : TimerSrc) (tl : Nat → TEv) (sch : Sched S.n tl),
    WF S C l t tl → Assumptions S C tl sch → ¬ Wins S tl sch

/-- The assumption with the given number, when it is the only one that can be dropped. The numbering is: 1 A1, 2 A2 coverage,
3 A3, 4 A4, 5 A5, 6 A6, 7 A7, 8 A8, 12 A2 intact unit, 13 A2 code protected, 14 A2 connectivity. -/
def OthersHold (i : Nat) (S : Sys) (C : Cost) (tl : Nat → TEv) (sch : Sched S.n tl) : Prop :=
  (i = 1 ∨ A1 S tl) ∧ (i = 2 ∨ A2cov S) ∧ (i = 13 ∨ A2code S) ∧ (i = 14 ∨ A2conn S) ∧ (i = 12 ∨ A2intact S tl) ∧
  (i = 3 ∨ A3 S C) ∧ (i = 4 ∨ A4 tl) ∧ (i = 5 ∨ A5 tl) ∧ (i = 6 ∨ A6 S tl sch) ∧ (i = 7 ∨ A7 S) ∧ (i = 8 ∨ A8 S tl sch)

/-- The assumption numbered `i` holds. -/
def HoldsAt (i : Nat) (S : Sys) (C : Cost) (tl : Nat → TEv) (sch : Sched S.n tl) : Prop :=
  match i with
  | 1 => A1 S tl
  | 2 => A2cov S
  | 3 => A3 S C
  | 4 => A4 tl
  | 5 => A5 tl
  | 6 => A6 S tl sch
  | 7 => A7 S
  | 8 => A8 S tl sch
  | 12 => A2intact S tl
  | 13 => A2code S
  | 14 => A2conn S
  | _ => True

/-- Assumption `i` is necessary: some well-formed system satisfies all the others, the adversary wins, and `i` fails. -/
def NecessaryAssumption (i : Nat) : Prop :=
  ∃ (S : Sys) (C : Cost) (l : Level) (t : TimerSrc) (tl : Nat → TEv) (sch : Sched S.n tl),
    WF S C l t tl ∧ OthersHold i S C tl sch ∧ Wins S tl sch ∧ ¬ HoldsAt i S C tl sch

/-- T3: each of the eleven assumptions (A1, A2 coverage, A2 code protected, A2 connectivity, A2 intact unit, A3, A4, A5, A6, A7, A8)
is necessary within this model: some well-formed system satisfies the other ten, has an adversary that wins, and violates it. -/
def AssumptionsNecessary : Prop :=
  NecessaryAssumption 1 ∧ NecessaryAssumption 2 ∧ NecessaryAssumption 3 ∧ NecessaryAssumption 4 ∧ NecessaryAssumption 5 ∧
  NecessaryAssumption 6 ∧ NecessaryAssumption 7 ∧ NecessaryAssumption 8 ∧ NecessaryAssumption 12 ∧ NecessaryAssumption 13 ∧
  NecessaryAssumption 14

/-- The toggle produced by the next iteration of the split-view kernel, whose opcode is fetched from the view `F`. -/
def ToggleAt (opAddr : Nat) (s : VState) : Nat := toggle (kAlu (s.F opAddr) s.sum (rd64 s.D s.ptr)).1

/-- A faithful run: the fetched opcode equals the data-view opcode at the start of each of the `n` iterations. -/
def FaithfulRun (opAddr : Nat) (med : Nat → Bool) : Nat → Nat → VState → Prop
  | _, 0, _ => True
  | i, n + 1, s => s.F opAddr = s.D opAddr ∧ FaithfulRun opAddr med (i + 1) n (vStep opAddr (med i) s)

/-- T2: a faithful run mediates every iteration whose toggle is non-zero (apart from the last), and under A3 and A5 a faithful
mediated check that the cost contract admits, with such an iteration, is a timing failure (its reading exceeds the threshold).
It does not say that every split-view attack is detected. -/
def MediationTheorem : Prop :=
  (∀ (opAddr : Nat) (med : Nat → Bool) (n i : Nat) (s : VState), FaithfulRun opAddr med i n s → ∀ j, j + 1 < n →
      ToggleAt opAddr (vRun opAddr med i j s) ≠ 0 → med (i + j) = true) ∧
  (∀ (S : Sys) (C : Cost) (tl : Nat → TEv), A3 S C → A5 tl → ∀ (c x : Nat) (med : Nat → Bool) (e r : Nat), x < S.n →
      tl c = TEv.check x (.mediated med) e r → C.admits S (tl c) → ∀ s0 : VState,
      FaithfulRun (S.unit x).cu.opAddr med 0 ((S.unit x).cu.size / 8) s0 → ∀ j, j + 1 < (S.unit x).cu.size / 8 →
      ToggleAt (S.unit x).cu.opAddr (vRun (S.unit x).cu.opAddr med 0 j s0) ≠ 0 → timeFailAt S tl c x)

/-- T4: what each level gives and loses, as the model's level capabilities define them. Every well-formed timeline at level L0 or
L1 with the inline timer satisfies A1, A4 and A5. Conversely there is a winning adversary against a system satisfying every
assumption except one (`OthersHold`, as in T3): at L1 with an operating-system timer and at L2 the one is A5, at L2 also A1, at L4
A4. The capabilities themselves are contract fields (`Level.allows`), not facts about a real system. -/
def LevelMatrix : Prop :=
  (∀ (S : Sys) (C : Cost) (l : Level) (tl : Nat → TEv), WF S C l .tsc tl → l.rank < 2 → A1 S tl ∧ A4 tl ∧ A5 tl) ∧
  (∃ (S : Sys) (C : Cost) (tl : Nat → TEv) (sch : Sched S.n tl),
      WF S C .L1 .osApi tl ∧ OthersHold 5 S C tl sch ∧ Wins S tl sch ∧ ¬ A5 tl) ∧
  (∃ (S : Sys) (C : Cost) (tl : Nat → TEv) (sch : Sched S.n tl),
      WF S C .L2 .tsc tl ∧ OthersHold 5 S C tl sch ∧ Wins S tl sch ∧ ¬ A5 tl) ∧
  (∃ (S : Sys) (C : Cost) (tl : Nat → TEv) (sch : Sched S.n tl),
      WF S C .L2 .tsc tl ∧ OthersHold 1 S C tl sch ∧ Wins S tl sch ∧ ¬ A1 S tl) ∧
  (∃ (S : Sys) (C : Cost) (tl : Nat → TEv) (sch : Sched S.n tl),
      WF S C .L4 .tsc tl ∧ OthersHold 4 S C tl sch ∧ Wins S tl sch ∧ ¬ A4 tl)

/-- C01 and C02 (supporting, not part of the selected Palomar statement: a general observation about observation-preserving
simulation, whose time bound assumes the per-read charge it uses). A Harvard machine reproducing the observation of a von Neumann machine on all memories reads every sensitive byte
the von Neumann machine reads, and a time bound that charges `ρ` per such read follows for any list of distinct sensitive bytes. -/
def HarvardSeparation : Prop :=
  ∀ {C S Obs : Type} (H : Harvard C) (V : VonNeumann S) (emb : S → C) (N : Nat) (obsH : C → Obs) (obsV : S → Obs),
    Simulates H V emb N obsH obsV → ∀ (s : S) (m : Mem),
      (∀ a, Sensitive V obsV s m a → a ∈ H.reads N (emb s) m) ∧
      ∀ (ss : List Nat), ss.Nodup → (∀ a, a ∈ ss → Sensitive V obsV s m a) → ∀ (ρ tV tH : Nat),
        tV + ρ * (H.reads N (emb s) m).length ≤ tH → tV + ρ * ss.length ≤ tH

end SmcTamper.Paper
