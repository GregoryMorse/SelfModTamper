module
public import SmcTamper.Spec.Harvard
public import SmcTamper.Bits.Bytes

@[expose] public section

namespace SmcTamper

/-- **Non-interference of Harvard machines.**  Two memories that agree on every address the run reads (computed on the
first) give the same final control and the same list of reads. -/
theorem harvard_noninterference {C : Type} (H : Harvard C) :
    ∀ (n : Nat) (c : C) (m1 m2 : Mem), (∀ a, a ∈ H.reads n c m1 → m1 a = m2 a) →
      (H.run n c m1).1 = (H.run n c m2).1 ∧ H.reads n c m1 = H.reads n c m2 := by
  intro n
  induction n with
  | zero => intro c m1 m2 _; simp [Harvard.run, Harvard.reads]
  | succ n ih =>
    intro c m1 m2 h
    have h0 : m1 (H.readAddr c) = m2 (H.readAddr c) := h _ (by simp [Harvard.reads])
    have hs : (H.step c m1).1 = (H.step c m2).1 := by simp [Harvard.step, h0]
    have hag : ∀ a, a ∈ H.reads n (H.step c m1).1 (H.step c m1).2 → (H.step c m1).2 a = (H.step c m2).2 a := by
      intro a ha
      have hin : a ∈ H.reads (n + 1) c m1 := by simp [Harvard.reads]; exact Or.inr ha
      have := h a hin
      simp only [Harvard.step]
      rw [← h0]
      cases hww : H.write c (m1 (H.readAddr c)) with
      | none => simpa [applyWrite] using this
      | some p =>
        obtain ⟨a', v⟩ := p
        by_cases hx : a = a'
        · simp [applyWrite, wr8, hx]
        · simp [applyWrite, wr8, hx, this]
    have ih' := ih (H.step c m1).1 (H.step c m1).2 (H.step c m2).2 hag
    have e1 : (H.run n (H.step c m2).1 (H.step c m2).2).1 = (H.run n (H.step c m1).1 (H.step c m2).2).1 := by rw [hs]
    have e2 : H.reads n (H.step c m2).1 (H.step c m2).2 = H.reads n (H.step c m1).1 (H.step c m2).2 := by rw [hs]
    refine ⟨?_, ?_⟩
    · simp only [Harvard.run]; rw [e1]; exact ih'.1
    · simp only [Harvard.reads]; rw [e2]; exact congrArg _ ih'.2

end SmcTamper
