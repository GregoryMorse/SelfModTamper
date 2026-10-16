module
public import SmcTamper.Spec.Contract
public import SmcTamper.Spec.Images

@[expose] public section

namespace SmcTamper

/-- **C14 (granule false positives).**  With a coarser granule a store to a byte used by no in-flight instruction still
clears: the store at `0x1005` and the instruction at `0x1028..0x102A` share a 64-byte line and a page but no byte. -/
theorem false_positive :
    ∃ tr : List Ev, clearCount 1 8 tr = 0 ∧ clearCount 64 8 tr = 1 ∧ clearCount 4096 8 tr = 1 :=
  ⟨[⟨0x2000, 4, some (0x1005, 1)⟩, ⟨0x1028, 3, none⟩], by decide, by decide, by decide⟩

/-- **C42 (design rule).**  If no store shares a granule with any of the next `W` events, there are no clears. -/
theorem no_clear_of_disjoint (g W : Nat) :
    ∀ tr : List Ev, (∀ pre e rest, tr = pre ++ e :: rest → ∀ a w, e.store = some (a, w) →
      ∀ f ∈ rest.take W, granHit g a w f.pc f.len = false) → clearCount g W tr = 0 := by
  intro tr
  induction tr with
  | nil => intro _; rfl
  | cons e rest ih =>
    intro h
    have h0 : clearsAhead g W e rest = false := by
      unfold clearsAhead
      cases hs : e.store with
      | none => rfl
      | some p =>
        obtain ⟨a, w⟩ := p
        simp only
        rw [Bool.eq_false_iff]
        intro hany
        obtain ⟨f, hf, hhit⟩ := List.any_eq_true.mp hany
        have := h [] e rest rfl a w hs f hf
        rw [this] at hhit; cases hhit
    have h1 : clearCount g W rest = 0 := by
      apply ih
      intro pre e' rest' hr a w hs f hf
      exact h (e :: pre) e' rest' (by rw [hr]; rfl) a w hs f hf
    simp [clearCount, h0, h1]

/-- Instructions that store to memory. -/
def isStoreInstr : Instr → Bool
  | .movStore .. => true
  | .xorMB .. => true
  | .aluMR32 .. => true
  | .aluMR64 .. => true
  | _ => false

/-- The intro executes three stores per pass (the displacement self-modification, the patch `XOR` and its restoring `SUB`);
the tail has four (the same three and the result store). Each store causes at most one clear, so these are the
"clears at the start of unrolled iterations" (C36). -/
theorem intro_stores : (introBody.filter isStoreInstr).length = 3 := by decide

theorem tail_stores : (tailBody.filter isStoreInstr).length = 4 := by decide

end SmcTamper
