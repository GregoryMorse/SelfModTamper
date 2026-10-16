module
public import SmcTamper.Spec.Contract
public import SmcTamper.Static.Loop

@[expose] public section

namespace SmcTamper

/-! ## C12: the naive static kernel clears about once per iteration

One iteration of Fig. 2 is ten instructions (`iterRips`, the instruction addresses `loop_run` extracts from the Level 2
run); the `XOR BYTE PTR [opcode], DL` is the seventh and stores into the first instruction (`ADC`) of the next
iteration, four events later. -/

def iterEvs (a0 : Nat) : List Ev :=
  [⟨a0 + 11, 3, none⟩, ⟨a0 + 14, 3, none⟩, ⟨a0 + 17, 3, none⟩, ⟨a0 + 20, 3, none⟩, ⟨a0 + 23, 2, none⟩,
   ⟨a0 + 25, 3, none⟩, ⟨a0 + 28, 6, some (a0 + 12, 1)⟩, ⟨a0 + 34, 4, none⟩, ⟨a0 + 38, 3, none⟩, ⟨a0 + 41, 2, none⟩]

def staticEvents (a0 n : Nat) : List Ev := (List.replicate n (iterEvs a0)).flatten

/-- The events' addresses are exactly the trace `loop_run` proves for the machine code. -/
theorem staticEvents_pcs (a0 n : Nat) : (staticEvents a0 n).map Ev.pc = (List.replicate n (iterRips a0)).flatten := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [staticEvents, List.replicate_succ, List.flatten_cons, List.map_append] at *; rw [ih]; rfl

theorem granHit_adc (g a0 : Nat) (hg : 1 ≤ g) : granHit g (a0 + 12) 1 (a0 + 11) 3 = true := by
  unfold granHit
  have h1 : (a0 + 12) / g ≤ (a0 + 11 + 3 - 1) / g := Nat.div_le_div_right (by omega)
  have h2 : (a0 + 11) / g ≤ (a0 + 12 + 1 - 1) / g := Nat.div_le_div_right (by omega)
  exact decide_eq_true (And.intro h1 h2)

theorem static_clear_aux (g W a0 : Nat) (R : List Ev) (hg : 1 ≤ g) (hW : 4 ≤ W) :
    clearCount g W (iterEvs a0 ++ (⟨a0 + 11, 3, none⟩ :: R)) = 1 + clearCount g W (⟨a0 + 11, 3, none⟩ :: R) := by
  obtain ⟨V, rfl⟩ : ∃ V, W = V + 4 := ⟨W - 4, by omega⟩
  have hc : clearsAhead g (V + 4) (⟨a0 + 28, 6, some (a0 + 12, 1)⟩ : Ev)
      (⟨a0 + 34, 4, none⟩ :: ⟨a0 + 38, 3, none⟩ :: ⟨a0 + 41, 2, none⟩ :: ⟨a0 + 11, 3, none⟩ :: R) = true := by
    unfold clearsAhead
    simp only
    rw [List.any_eq_true]
    refine ⟨⟨a0 + 11, 3, none⟩, ?_, granHit_adc g a0 hg⟩
    have e : V + 4 = (V + 3) + 1 := rfl
    simp [e, List.take_succ_cons]
  simp only [iterEvs, List.cons_append, List.nil_append, clearCount, hc]
  simp [clearsAhead]

theorem static_clear_step (g W a0 : Nat) (T : List Ev) (hg : 1 ≤ g) (hW : 4 ≤ W) :
    clearCount g W (iterEvs a0 ++ (iterEvs a0 ++ T)) = 1 + clearCount g W (iterEvs a0 ++ T) := by
  have := static_clear_aux g W a0 (⟨a0 + 14, 3, none⟩ :: ⟨a0 + 17, 3, none⟩ :: ⟨a0 + 20, 3, none⟩ :: ⟨a0 + 23, 2, none⟩ ::
    ⟨a0 + 25, 3, none⟩ :: ⟨a0 + 28, 6, some (a0 + 12, 1)⟩ :: ⟨a0 + 34, 4, none⟩ :: ⟨a0 + 38, 3, none⟩ ::
    ⟨a0 + 41, 2, none⟩ :: T) hg hW
  simpa [iterEvs] using this

/-- **C12.**  For any granule `g ≥ 1` and window `W ≥ 4`, the `n`-iteration naive kernel has at least `n − 1` clears
(the store of each iteration but the last lands in the first instruction of the next), hence costs at least `(n−1) κ`. -/
theorem static_clears_ge (g W a0 : Nat) (hg : 1 ≤ g) (hW : 4 ≤ W) :
    ∀ n, n - 1 ≤ clearCount g W (staticEvents a0 n) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    cases n with
    | zero => simp
    | succ n =>
      have e : staticEvents a0 (n + 2) = iterEvs a0 ++ (iterEvs a0 ++ staticEvents a0 n) := by
        simp [staticEvents, List.replicate_succ]
      have e' : staticEvents a0 (n + 1) = iterEvs a0 ++ staticEvents a0 n := by
        simp [staticEvents, List.replicate_succ]
      rw [e, static_clear_step g W a0 _ hg hW, ← e']
      omega

theorem static_time_ge (g W κ base a0 n : Nat) (hg : 1 ≤ g) (hW : 4 ≤ W) :
    κ * (n - 1) ≤ clearTime g W κ base (staticEvents a0 n) := by
  unfold clearTime
  have := Nat.mul_le_mul_left κ (static_clears_ge g W a0 hg hW n)
  omega

end SmcTamper
