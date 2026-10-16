module

@[expose] public section

namespace SmcTamper

/-! ## Scheduler and noise contract (platform contract item 4; C07, C43)

Per run of length `L` at most `⌊L/q⌋ + 1` clock interrupts of tick period `q` (each costing at most `δ`) occur; a run is
*disturbed* if its noise exceeds a threshold.  The deterministic form of the repetition assumption: at most `r` of any `k`
consecutive runs are disturbed, with `k > r`. -/

def maxInterrupts (L q : Nat) : Nat := L / q + 1

theorem maxInterrupts_mono (q : Nat) {L1 L2 : Nat} (h : L1 ≤ L2) : maxInterrupts L1 q ≤ maxInterrupts L2 q := by
  unfold maxInterrupts
  have := Nat.div_le_div_right (c := q) h
  omega

/-- Minimum of a non-empty sample (`x` is the first element). -/
def sampleMin (x : Nat) (xs : List Nat) : Nat := xs.foldl min x

theorem sampleMin_le (x : Nat) (xs : List Nat) : ∀ y, y ∈ x :: xs → sampleMin x xs ≤ y := by
  have key : ∀ (acc : Nat) (l : List Nat), (l.foldl min acc ≤ acc) ∧ ∀ y, y ∈ l → l.foldl min acc ≤ y := by
    intro acc l
    induction l generalizing acc with
    | nil => exact ⟨Nat.le_refl _, fun y hy => by cases hy⟩
    | cons z l ih =>
      obtain ⟨i1, i2⟩ := ih (min acc z)
      refine ⟨Nat.le_trans i1 (Nat.min_le_left _ _), ?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact Nat.le_trans i1 (Nat.min_le_right _ _)
      · exact i2 y hy
  intro y hy
  rcases List.mem_cons.mp hy with rfl | hy
  · exact (key _ xs).1
  · exact (key _ xs).2 y hy

def disturbedIn (dist : Nat → Bool) (s k : Nat) : Nat := (List.range k).countP (fun i => dist (s + i))

/-- **Repetition lemma (C07/C43).**  If at most `r` of the `k > r` consecutive runs starting at `s` are disturbed, some run in the
window is undisturbed. -/
theorem undisturbed_exists (dist : Nat → Bool) (r k s : Nat) (hk : r < k) (h : disturbedIn dist s k ≤ r) :
    ∃ i, i < k ∧ dist (s + i) = false := by
  refine Classical.byContradiction ?_
  intro hne
  have hall : ∀ i ∈ List.range k, dist (s + i) = true := by
    intro i hi
    have hi' := List.mem_range.mp hi
    cases hd : dist (s + i) with
    | true => rfl
    | false => exact absurd ⟨i, hi', hd⟩ hne
  have := (List.countP_eq_length (p := fun i => dist (s + i))).mpr hall
  unfold disturbedIn at h
  rw [this, List.length_range] at h
  omega

end SmcTamper
