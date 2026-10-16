module
public import SmcTamper.Spec.Harvard

@[expose] public section

namespace SmcTamper

/-! ## C01: a Harvard machine simulates any von Neumann machine step for step

The interpreter's control is the von Neumann state, a step counter and the bytes read so far in the current
von Neumann step.  It performs `L` fetch reads, `w` data reads and a final step that executes and writes
(`L + w + 1` Harvard steps), never fetching anything but data. -/

def recSet (r : Nat → BitVec 8) (k : Nat) (b : BitVec 8) : Nat → BitVec 8 := fun i => if i = k then b else r i

def VonNeumann.winOf {S : Type} (V : VonNeumann S) (r : Nat → BitVec 8) : Fin V.L → BitVec 8 := fun i => r i.val
def VonNeumann.dvOf {S : Type} (V : VonNeumann S) (r : Nat → BitVec 8) : Fin V.w → BitVec 8 := fun j => r (V.L + j.val)

def VonNeumann.interp {S : Type} (V : VonNeumann S) : Harvard (S × Nat × (Nat → BitVec 8)) where
  readAddr c :=
    if c.2.1 < V.L then V.pc c.1 + c.2.1
    else if h : c.2.1 - V.L < V.w then V.dataAddr c.1 (V.winOf c.2.2) ⟨c.2.1 - V.L, h⟩ else 0
  next c b :=
    if c.2.1 < V.L + V.w then (c.1, c.2.1 + 1, recSet c.2.2 c.2.1 b)
    else ((V.exec c.1 (V.winOf c.2.2) (V.dvOf c.2.2)).1, 0, fun _ => 0)
  write c _ :=
    if c.2.1 < V.L + V.w then none else (V.exec c.1 (V.winOf c.2.2) (V.dvOf c.2.2)).2

/-- The byte the interpreter reads at its `i`-th read of the von Neumann step from `s` on `m`. -/
def VonNeumann.truth {S : Type} (V : VonNeumann S) (s : S) (m : Mem) (i : Nat) : BitVec 8 :=
  if i < V.L then m (V.pc s + i)
  else if h : i - V.L < V.w then m (V.dataAddr s (fun j : Fin V.L => m (V.pc s + j.val)) ⟨i - V.L, h⟩) else 0

def VonNeumann.tr {S : Type} (V : VonNeumann S) (s : S) (m : Mem) (j : Nat) : Nat → BitVec 8 :=
  fun i => if i < j then V.truth s m i else 0

theorem Harvard.run_succ_right {C : Type} (H : Harvard C) :
    ∀ (n : Nat) (c : C) (m : Mem), H.run (n + 1) c m = H.step (H.run n c m).1 (H.run n c m).2 := by
  intro n
  induction n with
  | zero => intro c m; simp [Harvard.run]
  | succ n ih => intro c m; rw [Harvard.run, ih (H.step c m).1 (H.step c m).2]; rfl

theorem tr_win {S : Type} (V : VonNeumann S) (s : S) (m : Mem) (j : Nat) (hj : V.L ≤ j) :
    V.winOf (V.tr s m j) = fun i : Fin V.L => m (V.pc s + i.val) := by
  funext i
  have : i.val < j := by have := i.isLt; omega
  simp [VonNeumann.winOf, VonNeumann.tr, this, VonNeumann.truth, i.isLt]

theorem tr_dv {S : Type} (V : VonNeumann S) (s : S) (m : Mem) (j : Nat) (hj : V.L + V.w ≤ j) :
    V.dvOf (V.tr s m j) = fun i : Fin V.w => m (V.dataAddr s (fun j : Fin V.L => m (V.pc s + j.val)) i) := by
  funext i
  have h1 : V.L + i.val < j := by have := i.isLt; omega
  have h2 : ¬ V.L + i.val < V.L := by omega
  have h3 : V.L + i.val - V.L < V.w := by have := i.isLt; omega
  simp only [VonNeumann.dvOf, VonNeumann.tr, h1, if_true, VonNeumann.truth, h2, if_false, dif_pos h3]
  congr 2
  apply Fin.ext
  simp

theorem interp_prefix {S : Type} (V : VonNeumann S) (s : S) (m : Mem) :
    ∀ j, j ≤ V.L + V.w → V.interp.run j (s, 0, V.tr s m 0) m = ((s, j, V.tr s m j), m) := by
  intro j
  induction j with
  | zero => intro _; simp [Harvard.run]
  | succ j ih =>
    intro hj
    have hj' : j < V.L + V.w := by omega
    rw [Harvard.run_succ_right, ih (by omega)]
    have hbyte : m (V.interp.readAddr (s, j, V.tr s m j)) = V.truth s m j := by
      by_cases hL : j < V.L
      · simp [VonNeumann.interp, hL, VonNeumann.truth]
      · have h3 : j - V.L < V.w := by omega
        simp only [VonNeumann.interp, hL, if_false, dif_pos h3, VonNeumann.truth]
        rw [tr_win V s m j (by omega)]
    have hnext : V.interp.next (s, j, V.tr s m j) (V.truth s m j) = (s, j + 1, V.tr s m (j + 1)) := by
      simp only [VonNeumann.interp, hj', if_true]
      refine congrArg (fun r => (s, j + 1, r)) ?_
      funext i
      by_cases hi : i = j
      · subst hi; simp [recSet, VonNeumann.tr]
      · have : (i < j + 1) = (i < j) := by
          apply propext; constructor <;> intro h <;> omega
        simp [recSet, VonNeumann.tr, hi, this]
    have hwr : V.interp.write (s, j, V.tr s m j) (V.truth s m j) = none := by
      simp [VonNeumann.interp, hj']
    simp only [Harvard.step, hbyte, hnext, hwr, applyWrite]

theorem tr_zero {S : Type} (V : VonNeumann S) (s : S) (m : Mem) : V.tr s m 0 = fun _ => 0 := by
  funext i; simp [VonNeumann.tr]

/-- **C01 (interpreter).**  From the embedding of a von Neumann state, the Harvard interpreter performs exactly
`L + w + 1` steps, reads only data addresses, and reaches the embedding of the successor state with the successor
memory.  No instruction is ever fetched from the memory it writes. -/
theorem interp_step {S : Type} (V : VonNeumann S) (s : S) (m : Mem) :
    V.interp.run (V.L + V.w + 1) (s, 0, fun _ => 0) m = (((V.step s m).1, 0, fun _ => 0), (V.step s m).2) := by
  have h := interp_prefix V s m (V.L + V.w) (Nat.le_refl _)
  rw [Harvard.run_succ_right, ← tr_zero V s m, h]
  have hr : ¬ (V.L + V.w < V.L + V.w) := Nat.lt_irrefl _
  have hwin := tr_win V s m (V.L + V.w) (by omega)
  have hdv := tr_dv V s m (V.L + V.w) (Nat.le_refl _)
  simp only [Harvard.step, VonNeumann.interp, hr, if_false, hwin, hdv, VonNeumann.step]
  rfl

/-- `interp` simulates `V` in the sense of `Simulates` (observation: the state), with `L + w + 1` steps per step. -/
theorem interp_simulates {S : Type} (V : VonNeumann S) :
    Simulates V.interp V (fun s => (s, 0, fun _ => 0)) (V.L + V.w + 1) (fun c => c.1) (fun s => s) := by
  intro s m
  rw [interp_step]

end SmcTamper
