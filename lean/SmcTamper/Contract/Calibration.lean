module
public import SmcTamper.Contract.Noise

@[expose] public section

namespace SmcTamper

/-! ## Calibration by the sample maximum: the counting core (gap G14)

If `m` timing samples are exchangeable (every ordering equally likely), the chance that a given one exceeds all the others is at most `1/m`,
because in any fixed assignment of `m` values at most one position is a strict maximum.  That counting fact is what is proved; the
probability statement itself needs a measure and is **not** formalised and not claimed (the independence of runs is a platform
assumption, `Contract/Noise`).  With `m = n + 1` it is the false-alarm bound `1/(n+1)` for a threshold taken as the maximum of `n`
calibration runs. -/

/-- Position `i` of the sample `a` holds a value strictly above every other position's. -/
def StrictMaxAt (a : Nat → Nat) (m i : Nat) : Prop := i < m ∧ ∀ j, j < m → j ≠ i → a j < a i

theorem strictMaxAt_unique (a : Nat → Nat) (m i j : Nat) (hi : StrictMaxAt a m i) (hj : StrictMaxAt a m j) : i = j := by
  by_cases h : i = j
  · exact h
  · have h1 := hi.2 j hj.1 (fun e => h e.symm)
    have h2 := hj.2 i hi.1 h
    omega

open Classical in
/-- At most one of the `m` positions is a strict maximum. -/
theorem strictMax_count_le_one (a : Nat → Nat) (m : Nat) :
    (List.range m).countP (fun i => decide (StrictMaxAt a m i)) ≤ 1 := by
  rw [List.countP_eq_length_filter]
  have hnd : ((List.range m).filter (fun i => decide (StrictMaxAt a m i))).Nodup := List.nodup_range.filter _
  have hmem : ∀ x ∈ (List.range m).filter (fun i => decide (StrictMaxAt a m i)), StrictMaxAt a m x := by
    intro x hx
    simpa using (List.mem_filter.mp hx).2
  generalize (List.range m).filter (fun i => decide (StrictMaxAt a m i)) = l at hnd hmem
  match l, hnd, hmem with
  | [], _, _ => simp
  | [_], _, _ => simp
  | x :: y :: t, hnd, hmem =>
    exfalso
    have hxy := strictMaxAt_unique a m x y (hmem x (by simp)) (hmem y (by simp))
    have := (List.nodup_cons.mp hnd).1
    exact this (by simp [hxy])

open Classical in
/-- A threshold that is at least the largest of the other `n` samples is exceeded only by a strict maximum; so at most one of the `n + 1`
positions can be the sample that exceeds the (maximum of the) other `n`. -/
theorem exceeds_others_le_one (a : Nat → Nat) (n : Nat) :
    (List.range (n + 1)).countP (fun i => decide (∀ j, j < n + 1 → j ≠ i → a j < a i)) ≤ 1 := by
  have := strictMax_count_le_one a (n + 1)
  simp only [StrictMaxAt] at this
  refine Nat.le_trans (List.countP_mono_left ?_) this
  intro i hi h
  simp only [decide_eq_true_eq] at h
  have hi' := List.mem_range.mp hi
  simpa [hi'] using h

end SmcTamper
