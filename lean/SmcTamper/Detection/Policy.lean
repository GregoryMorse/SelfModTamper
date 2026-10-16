module
public import SmcTamper.Spec.Detection
public import SmcTamper.Contract.Noise

@[expose] public section

namespace SmcTamper

/-! ## C45: the `k`-consecutive-failures policy and the threshold

`ok t` says that run `t` passed `P`.  The alarm fires after `k` consecutive failures. -/

/-- **No false alarm under the deterministic noise contract.**  If every run that passes the value check and is undisturbed
passes `P`, the value check always passes (unmodified code), and of any `k` consecutive runs at most `r < k` are disturbed, the
alarm never fires. -/
theorem no_false_alarm (k r : Nat) (disturbed ok : Nat → Bool) (hk : r < k)
    (hwin : ∀ s, disturbedIn disturbed s k ≤ r)
    (hundist : ∀ t, disturbed t = false → ok t = true) (t : Nat) : ¬ alarm k ok t := by
  intro ⟨hkt, hfail⟩
  obtain ⟨i, hi, hd⟩ := undisturbed_exists disturbed r k (t + 1 - k) hk (hwin _)
  have hok := hundist _ hd
  have := hfail (k - 1 - i) (by omega)
  have e : t - (k - 1 - i) = t + 1 - k + i := by omega
  rw [e, hok] at this
  cases this

/-- **Persistent slowdown is detected within `k` runs.**  If every run from `s` on fails, the alarm fires at run `s + k − 1`. -/
theorem alarm_of_persistent (k : Nat) (ok : Nat → Bool) (s : Nat) (hk : 0 < k) (h : ∀ t, s ≤ t → ok t = false) :
    alarm k ok (s + k - 1) := by
  refine ⟨by omega, ?_⟩
  intro i hi
  exact h _ (by omega)

/-- Maximum of a non-empty calibration sample (`x` is the first element). -/
def sampleMax (x : Nat) (xs : List Nat) : Nat := xs.foldl max x

theorem le_sampleMax (x : Nat) (xs : List Nat) : ∀ y, y ∈ x :: xs → y ≤ sampleMax x xs := by
  have key : ∀ (acc : Nat) (l : List Nat), (acc ≤ l.foldl max acc) ∧ ∀ y, y ∈ l → y ≤ l.foldl max acc := by
    intro acc l
    induction l generalizing acc with
    | nil => exact ⟨Nat.le_refl _, fun y hy => by cases hy⟩
    | cons z l ih =>
      obtain ⟨i1, i2⟩ := ih (max acc z)
      refine ⟨Nat.le_trans (Nat.le_max_left _ _) i1, ?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact Nat.le_trans (Nat.le_max_right _ _) i1
      · exact i2 y hy
  intro y hy
  rcases List.mem_cons.mp hy with rfl | hy
  · exact (key _ xs).1
  · exact (key _ xs).2 y hy

/-- **Calibration.**  A threshold at least the maximum of the calibration samples rejects none of them on time. -/
theorem calibration_no_alarm (x : Nat) (xs : List Nat) (τ : Nat) (hτ : sampleMax x xs ≤ τ) :
    ∀ y, y ∈ x :: xs → y ≤ τ := fun y hy => Nat.le_trans (le_sampleMax x xs y hy) hτ

end SmcTamper
