module
public import SmcTamper.Harvard.NonInterference

@[expose] public section

namespace SmcTamper

theorem reads_length {C : Type} (H : Harvard C) : ∀ (n : Nat) (c : C) (m : Mem), (H.reads n c m).length = n := by
  intro n
  induction n with
  | zero => intro c m; rfl
  | succ n ih => intro c m; simp [Harvard.reads, ih]

/-- **C02 (separation).**  A Harvard machine that reproduces the observation of a von Neumann machine on all memories
reads every sensitive byte that the von Neumann machine fetches or reads. -/
theorem harvard_reads_sensitive {C S Obs : Type} (H : Harvard C) (V : VonNeumann S) (emb : S → C) (N : Nat)
    (obsH : C → Obs) (obsV : S → Obs) (hsim : Simulates H V emb N obsH obsV) (s : S) (m : Mem) (a : Nat)
    (hsens : Sensitive V obsV s m a) : a ∈ H.reads N (emb s) m := by
  obtain ⟨v, hv⟩ := hsens
  refine Classical.byContradiction ?_
  intro hna
  have hag : ∀ x, x ∈ H.reads N (emb s) m → m x = wr8 m a v x := by
    intro x hx
    have : x ≠ a := fun h => hna (h ▸ hx)
    rw [wr8_other _ _ _ _ this]
  have h1 := (harvard_noninterference H N (emb s) m (wr8 m a v) hag).1
  apply hv
  rw [← hsim s m, ← hsim s (wr8 m a v), h1]

/-- **C02, quantitative corollary under the cost contract.**  If every data read costs at least `ρ` beyond the native
(von Neumann) time `tV`, i.e. `tV + ρ · #reads ≤ tH`, and `ss` lists `k` distinct sensitive bytes, then
`tV + ρ · k ≤ tH`. -/
theorem harvard_time_bound {C S Obs : Type} (H : Harvard C) (V : VonNeumann S) (emb : S → C) (N : Nat)
    (obsH : C → Obs) (obsV : S → Obs) (hsim : Simulates H V emb N obsH obsV) (s : S) (m : Mem)
    (ss : List Nat) (hnd : ss.Nodup) (hss : ∀ a, a ∈ ss → Sensitive V obsV s m a)
    (ρ tV tH : Nat) (hT : tV + ρ * (H.reads N (emb s) m).length ≤ tH) : tV + ρ * ss.length ≤ tH := by
  have hsub : ∀ a, a ∈ ss → a ∈ H.reads N (emb s) m := fun a ha => harvard_reads_sensitive H V emb N obsH obsV hsim s m a (hss a ha)
  have hl : ss.length ≤ (H.reads N (emb s) m).length := hnd.length_le_of_subset hsub
  have := Nat.mul_le_mul_left ρ hl
  omega

end SmcTamper
