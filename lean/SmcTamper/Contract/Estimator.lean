module

@[expose] public section

namespace SmcTamper

/-! ## The disturbed-run estimator (C35, P01)

The driver reports integer statistics of `N` run times `xs`: `avg = ⌊Σ/N⌋`, `min`, `max`.  The paper estimates the number of
"disturbed" runs as `N (avg − min) / max`.  Below: what the three statistics do bound. -/

def excess (m : Nat) (xs : List Nat) : Nat := (xs.map (· - m)).sum

theorem excess_add_min (m : Nat) (xs : List Nat) (h : ∀ x ∈ xs, m ≤ x) : excess m xs + xs.length * m = xs.sum := by
  induction xs with
  | nil => simp [excess]
  | cons x xs ih =>
    have hx := h x (List.mem_cons_self ..)
    have ih' := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [excess, List.map_cons, List.sum_cons, List.length_cons] at ih' ⊢
    rw [Nat.add_mul]
    omega

/-- Each run above the minimum contributes at most `max − min` of the excess. -/
theorem excess_le_count (m M : Nat) (xs : List Nat) (h : ∀ x ∈ xs, m ≤ x ∧ x ≤ M) :
    excess m xs ≤ (xs.filter (fun x => decide (m < x))).length * (M - m) := by
  induction xs with
  | nil => simp [excess]
  | cons x xs ih =>
    have hx := h x (List.mem_cons_self ..)
    have ih' := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [excess, List.map_cons, List.sum_cons] at ih' ⊢
    by_cases hlt : m < x
    · rw [List.filter_cons_of_pos (by simpa using hlt), List.length_cons, Nat.add_mul]
      omega
    · rw [List.filter_cons_of_neg (by simpa using hlt)]
      have : x - m = 0 := by omega
      omega

/-- **Rigorous lower bound.**  With `avg = ⌊Σ/N⌋`: `N (avg − min) ≤ #{runs > min} · (max − min)`. -/
theorem count_above_min_lower (m M avg : Nat) (xs : List Nat) (h : ∀ x ∈ xs, m ≤ x ∧ x ≤ M)
    (havg : avg = xs.sum / xs.length) :
    xs.length * (avg - m) ≤ (xs.filter (fun x => decide (m < x))).length * (M - m) := by
  have h1 := excess_add_min m xs (fun x hx => (h x hx).1)
  have h2 := excess_le_count m M xs h
  have h3 : xs.length * avg ≤ xs.sum := by
    rw [havg, Nat.mul_comm]; exact Nat.div_mul_le_self _ _
  have h4 : xs.length * (avg - m) = xs.length * avg - xs.length * m := Nat.mul_sub _ _ _
  omega

/-- Two-point model (each run takes `min` or `max`): the number of `max` runs `k` satisfies `k (max − min) = Σ (x − min)`. -/
theorem two_point (m M : Nat) (xs : List Nat) (h : ∀ x ∈ xs, x = m ∨ x = M) :
    excess m xs = (xs.filter (fun x => decide (x = M))).length * (M - m) := by
  induction xs with
  | nil => simp [excess]
  | cons x xs ih =>
    have hx := h x (List.mem_cons_self ..)
    have ih' := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [excess, List.map_cons, List.sum_cons] at ih' ⊢
    by_cases hM : x = M
    · rw [List.filter_cons_of_pos (by simpa using hM), List.length_cons, Nat.add_mul]
      omega
    · rw [List.filter_cons_of_neg (by simpa using hM)]
      have : x = m := by omega
      subst this
      omega

/-- Markov: the runs at least `θ` above the minimum number at most `Σ (x − min) / θ`. -/
theorem markov_count (m θ : Nat) (xs : List Nat) (hθ : 0 < θ) (h : ∀ x ∈ xs, m ≤ x) :
    (xs.filter (fun x => decide (m + θ ≤ x))).length * θ ≤ excess m xs := by
  induction xs with
  | nil => simp [excess]
  | cons x xs ih =>
    have hx := h x (List.mem_cons_self ..)
    have ih' := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [excess, List.map_cons, List.sum_cons] at ih' ⊢
    by_cases hge : m + θ ≤ x
    · rw [List.filter_cons_of_pos (by simpa using hge), List.length_cons, Nat.add_mul]
      omega
    · rw [List.filter_cons_of_neg (by simpa using hge)]
      omega

/-- The paper's expression `N (avg − min) / max` is Markov's bound with `θ = max`: no run is `max` above a positive minimum, so it
bounds the size of an empty set and says nothing about the disturbed runs. -/
theorem published_estimate_vacuous (m M : Nat) (xs : List Nat) (hm : 0 < m) (h : ∀ x ∈ xs, x ≤ M) :
    (xs.filter (fun x => decide (m + M ≤ x))).length = 0 := by
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro x hx
  have := h x hx
  simp only [decide_eq_true_eq]
  omega

/-- P01, the printed values (Table 5, RDTSCP): `10000 (467286 − 414188) / 2158056 = 246` and, for the non-SMC column,
`⌊10000 (42300840 − 39600010) / 74295022⌋ = 363`. -/
theorem published_values :
    10000 * (467286 - 414188) / 2158056 = 246 ∧ 10000 * (42300840 - 39600010) / 74295022 = 363 := by decide

/-- P01, rigorous: any 10 000 runs with these statistics (SMC dynamic, RDTSCP) include at least 305 runs above the minimum
(`≥ 3.05 %`), and the non-SMC column at least 779 (`≥ 7.79 %`). The two-point model gives `304.49` and `778.4`. -/
theorem p01_smc (xs : List Nat) (hN : xs.length = 10000) (h : ∀ x ∈ xs, 414188 ≤ x ∧ x ≤ 2158056)
    (havg : 467286 = xs.sum / xs.length) : 305 ≤ (xs.filter (fun x => decide (414188 < x))).length := by
  have := count_above_min_lower 414188 2158056 467286 xs h havg
  rw [hN] at this
  omega

theorem p01_nonsmc (xs : List Nat) (hN : xs.length = 10000) (h : ∀ x ∈ xs, 39600010 ≤ x ∧ x ≤ 74295022)
    (havg : 42300840 = xs.sum / xs.length) : 779 ≤ (xs.filter (fun x => decide (39600010 < x))).length := by
  have := count_above_min_lower 39600010 74295022 42300840 xs h havg
  rw [hN] at this
  omega

/-- The two-point estimates (not integers: the two-point model cannot be exact). -/
theorem p01_two_point_values :
    10000 * (467286 - 414188) / (2158056 - 414188) = 304 ∧ 10000 * (42300840 - 39600010) / (74295022 - 39600010) = 778 := by decide

end SmcTamper
