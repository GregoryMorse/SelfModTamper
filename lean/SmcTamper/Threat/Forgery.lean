module
public import SmcTamper.Static.Emulation
public import SmcTamper.Detection.Predicate

@[expose] public section

namespace SmcTamper

/-! ## Compensation forgery for the single-site kernel (A8 necessity, P04)

The kernel's data-dependent state is the pair (sum, operation number `op`), `op ∈ {0, 1, 4, 5}` meaning ADC, SBB, XOR, CMP
(`cSwitch`).  A step with the data quadword `v` computes `r = cSwitch op sum v`, takes `r.2` as the new sum and `op ^ toggle r.1` as the
new operation number.  An adversary that controls three consecutive data quadwords after its last other modification can steer the
state to any target that an honest run from the canonical start can reach; two quadwords do not always suffice.  The one state that no
honest run reaches is `(S, CMP)` with `toggle S = 0` (CMP keeps the sum, so it can only be entered from CMP itself).  The numbers are
from the abstract machine, which `static_eq_c` ties to the assembled kernel. -/

def absStep (s : BitVec 64 × Nat) (v : BitVec 64) : BitVec 64 × Nat :=
  ((cSwitch s.2 s.1 v).2, cOpNext s.2 (cSwitch s.2 s.1 v).1)

def absRun : List (BitVec 64) → BitVec 64 × Nat → BitVec 64 × Nat
  | [], s => s
  | v :: vs, s => absRun vs (absStep s v)

theorem absStep_op (s : BitVec 64 × Nat) (v : BitVec 64) :
    (absStep s v).2 = s.2 ^^^ toggle (cSwitch s.2 s.1 v).1 := cOpNext_eq _ _

theorem absStep_isOp (s : BitVec 64 × Nat) (h : IsOp s.2) (v : BitVec 64) : IsOp (absStep s v).2 := by
  rw [absStep_op]; exact isOp_xor_toggle _ h _

theorem absRun_isOp (vs : List (BitVec 64)) : ∀ (s : BitVec 64 × Nat), IsOp s.2 → IsOp (absRun vs s).2 := by
  induction vs with
  | nil => intro s h; exact h
  | cons v vs ih => intro s h; exact ih _ (absStep_isOp s h v)

theorem isOp_xor (a b : Nat) (ha : IsOp a) (hb : IsOp b) : IsOp (a ^^^ b) := by
  unfold IsOp at *
  rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;> decide

theorem xor_cancel (a b : Nat) : a ^^^ b ^^^ b = a := by
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem exists_toggle (t : Nat) (h : IsOp t) : ∃ r : BitVec 64, toggle r = t := by
  unfold IsOp at h
  rcases h with rfl | rfl | rfl | rfl
  · exact ⟨1, by decide⟩
  · exact ⟨0x8000000000000001, by decide⟩
  · exact ⟨0, by decide⟩
  · exact ⟨0x8000000000000000, by decide⟩

/-- Any ALU result `r` can be produced from any sum by a suitable data quadword; CMP leaves the sum unchanged. -/
theorem exists_land (S : BitVec 64) (op : Nat) (h : IsOp op) (r : BitVec 64) :
    ∃ v, (cSwitch op S v).1 = r ∧ (cSwitch op S v).2 = (if op = 5 then S else r) := by
  unfold IsOp at h
  rcases h with rfl | rfl | rfl | rfl
  · exact ⟨r - S, by simp [cSwitch]; bv_omega, by simp [cSwitch]; bv_omega⟩
  · exact ⟨S - r, by simp [cSwitch]; bv_omega, by simp [cSwitch]; bv_omega⟩
  · exact ⟨S ^^^ r, by simp [cSwitch, ← BitVec.xor_assoc], by simp [cSwitch, ← BitVec.xor_assoc]⟩
  · exact ⟨S - r, by simp [cSwitch]; bv_omega, by simp [cSwitch]⟩

/-- One step can set the operation number to any of the four values, from any state. -/
theorem step_to_op (s : BitVec 64 × Nat) (hs : IsOp s.2) (o : Nat) (ho : IsOp o) :
    ∃ v, (absStep s v).2 = o := by
  obtain ⟨r, hr⟩ := exists_toggle (s.2 ^^^ o) (isOp_xor _ _ hs ho)
  obtain ⟨v, hv, _⟩ := exists_land s.1 s.2 hs r
  refine ⟨v, ?_⟩
  rw [absStep_op, hv, hr, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

/-- From a non-CMP state one step lands on any sum. -/
theorem step_noncmp (S : BitVec 64) (op : Nat) (h : IsOp op) (hne : op ≠ 5) (T : BitVec 64) :
    ∃ v, absStep (S, op) v = (T, op ^^^ toggle T) := by
  obtain ⟨v, hv1, hv2⟩ := exists_land S op h T
  refine ⟨v, ?_⟩
  simp only [absStep]
  rw [hv1, hv2, if_neg hne, cOpNext_eq]

/-- From CMP one step keeps the sum and sets the operation number to any of the four values. -/
theorem step_cmp (S : BitVec 64) (o : Nat) (ho : IsOp o) : ∃ v, absStep (S, 5) v = (S, o) := by
  obtain ⟨r, hr⟩ := exists_toggle (5 ^^^ o) (isOp_xor _ _ (by simp [IsOp]) ho)
  obtain ⟨v, hv1, hv2⟩ := exists_land S 5 (by simp [IsOp]) r
  refine ⟨v, ?_⟩
  simp only [absStep]
  rw [hv1, hv2, cOpNext_eq, hr, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  simp

/-- The invariant of honest runs: `(S, CMP)` with `toggle S = 0` is never entered. -/
def HInv (s : BitVec 64 × Nat) : Prop := IsOp s.2 ∧ (s.2 = 5 → toggle s.1 ≠ 0)

theorem inv_step (s : BitVec 64 × Nat) (hs : HInv s) (v : BitVec 64) : HInv (absStep s v) := by
  obtain ⟨hop, hcmp⟩ := hs
  refine ⟨absStep_isOp s hop v, ?_⟩
  intro h5
  obtain ⟨S, op⟩ := s
  simp only at hop hcmp
  rw [absStep_op] at h5
  simp only [absStep]
  unfold IsOp at hop
  rcases hop with rfl | rfl | rfl | rfl
  · simp only [cSwitch] at h5 ⊢
    intro hz
    rw [hz] at h5
    simp at h5
  · simp only [cSwitch] at h5 ⊢
    intro hz
    rw [hz] at h5
    simp at h5
  · simp only [cSwitch] at h5 ⊢
    intro hz
    rw [hz] at h5
    simp at h5
  · simp only [cSwitch]
    exact hcmp rfl

theorem inv_run (vs : List (BitVec 64)) : ∀ s, HInv s → HInv (absRun vs s) := by
  induction vs with
  | nil => intro s h; exact h
  | cons v vs ih => intro s h; exact ih _ (inv_step s h v)

theorem inv_start : HInv (0, 0) := ⟨by simp [IsOp], by simp⟩

/-- A target is *reachable* if an honest run (some data) from the canonical start (sum `0`, ADC) ends there. -/
def Reachable (t : BitVec 64 × Nat) : Prop := ∃ vs, absRun vs (0, 0) = t

theorem reachable_inv (t : BitVec 64 × Nat) (h : Reachable t) : HInv t := by
  obtain ⟨vs, rfl⟩ := h
  exact inv_run vs _ inv_start

/-- **Forgery with three quadwords.**  From any state of the kernel, three adversary-chosen data quadwords reach every target that an
honest run reaches. -/
theorem forgery_three (s : BitVec 64 × Nat) (hs : IsOp s.2) (t : BitVec 64 × Nat) (ht : Reachable t) :
    ∃ v1 v2 v3, absRun [v1, v2, v3] s = t := by
  obtain ⟨hto, hreach⟩ := reachable_inv t ht
  obtain ⟨T, ot⟩ := t
  simp only at hto hreach
  by_cases hg : ot ^^^ toggle T = 5
  · -- the last step is a CMP step from `(T, CMP)`, which is entered from a non-CMP state, so `toggle T ≠ 0`
    have hT : toggle T ≠ 0 := by
      intro h0
      rw [h0, Nat.xor_zero] at hg
      exact hreach hg h0
    have ho1 : IsOp (5 ^^^ toggle T) := isOp_xor _ _ (by simp [IsOp]) (toggle_isOp T)
    have hn1 : (5 ^^^ toggle T) ≠ 5 := by
      rcases toggle_isOp T with h | h | h | h <;> rw [h] <;> first | decide | (exfalso; exact hT h)
    obtain ⟨v1, hv1⟩ := step_to_op s hs (5 ^^^ toggle T) ho1
    obtain ⟨v2, hv2⟩ := step_noncmp (absStep s v1).1 (5 ^^^ toggle T) ho1 hn1 T
    obtain ⟨v3, hv3⟩ := step_cmp T ot hto
    refine ⟨v1, v2, v3, ?_⟩
    have e1 : absStep s v1 = ((absStep s v1).1, 5 ^^^ toggle T) := Prod.ext rfl hv1
    simp only [absRun]
    rw [e1, hv2, xor_cancel, hv3]
  · have hg' : IsOp (ot ^^^ toggle T) := isOp_xor _ _ hto (toggle_isOp T)
    obtain ⟨v1, hv1⟩ : ∃ v, True := ⟨0, trivial⟩
    have hs1 : IsOp (absStep s v1).2 := absStep_isOp s hs v1
    obtain ⟨v2, hv2⟩ := step_to_op (absStep s v1) hs1 (ot ^^^ toggle T) hg'
    obtain ⟨v3, hv3⟩ := step_noncmp (absStep (absStep s v1) v2).1 (ot ^^^ toggle T) hg' hg T
    refine ⟨v1, v2, v3, ?_⟩
    have e2 : absStep (absStep s v1) v2 = ((absStep (absStep s v1) v2).1, ot ^^^ toggle T) := Prod.ext rfl hv2
    simp only [absRun]
    rw [e2, hv3, xor_cancel]

/-! ### Two quadwords do not suffice -/

/-- The target `(2^63 + 1, XOR)`: reachable from the canonical start in three steps (`0`, `2^63 + 1`, `0`). -/
def tgt : BitVec 64 × Nat := (0x8000000000000001, 4)

theorem tgt_reachable : Reachable tgt := ⟨[0, 0x8000000000000001, 0], by decide⟩

/-- From the canonical state, no two data quadwords reach `tgt`: its last step must be a CMP step from `(2^63 + 1, CMP)` or a
non-CMP step from `(·, CMP xor toggle)`, and neither is reachable in one step from `(0, ADC)`. -/
theorem two_not_enough : ∀ v1 v2 : BitVec 64, absRun [v1, v2] (0, 0) ≠ tgt := by
  intro v1 v2 h
  have hT : toggle (0x8000000000000001 : BitVec 64) = 1 := by decide
  have h1 : absStep (0, 0) v1 = (v1, toggle v1) := by
    simp [absStep, cSwitch, cOpNext_eq]
  simp only [absRun, h1] at h
  have hop := toggle_isOp v1
  unfold IsOp at hop
  rcases hop with h0 | h0 | h0 | h0 <;>
  · simp only [tgt, absStep, h0, cSwitch, cOpNext_eq] at h
    obtain ⟨hs, ho⟩ := Prod.mk.inj h
    first
      | (rw [hs, hT] at ho; revert ho; decide)
      | (rw [hs, hT] at h0; revert h0; decide)


/-! ### From the abstract machine to the kernel

`tpCompC` (the transcribed Fig. 3 loop) reads the data qwords `rd64 m (p0 + 8 k)`; away from the opcode qword it is `absRun` of those
qwords.  Together with `static_eq_c` this is the assembled kernel's behaviour. -/

def qwList (m : Mem) (p n : Nat) : List (BitVec 64) := (List.range n).map (fun k => rd64 m (p + 8 * k))

theorem absRun_append (xs ys : List (BitVec 64)) (s : BitVec 64 × Nat) : absRun (xs ++ ys) s = absRun ys (absRun xs s) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => exact ih _

theorem qwList_succ (m : Mem) (p n : Nat) : qwList m p (n + 1) = qwList m p n ++ [rd64 m (p + 8 * n)] := by
  unfold qwList
  rw [List.range_succ, List.map_append]
  rfl

theorem tpCompCIter_abs (m : Mem) (opAddr : Nat) : ∀ (n : Nat) (c : CState), (∀ k, k < n → c.p + 8 * k ≠ opAddr / 8 * 8) →
    ((tpCompCIter m opAddr n c).sum, (tpCompCIter m opAddr n c).op) = absRun (qwList m c.p n) (c.sum, c.op) := by
  intro n
  induction n with
  | zero => intro c _; rfl
  | succ n ih =>
    intro c hc
    have h0 : c.p ≠ opAddr / 8 * 8 := by simpa using hc 0 (by omega)
    have hstep : tpCompCStep m opAddr c = ⟨c.p + 8, (absStep (c.sum, c.op) (rd64 m c.p)).1, (absStep (c.sum, c.op) (rd64 m c.p)).2⟩ := by
      simp [tpCompCStep, h0, absStep]
    have hlist : qwList m c.p (n + 1) = rd64 m c.p :: qwList m (c.p + 8) n := by
      unfold qwList
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      simp only [Nat.add_zero, Nat.mul_zero]
      congr 1
      apply List.map_congr_left
      intro k _
      simp only [Function.comp]
      congr 1
      omega
    show ((tpCompCIter m opAddr n (tpCompCStep m opAddr c)).sum, (tpCompCIter m opAddr n (tpCompCStep m opAddr c)).op) = _
    rw [ih _ (by rw [hstep]; intro k hk; have := hc (k + 1) (by omega); simp only; omega), hstep, hlist]
    rfl

/-- Bytes of a quadword. -/
def qbyte (v : BitVec 64) (j : Nat) : BitVec 8 := (v >>> (8 * j)).setWidth 8

theorem rd64_bytes (m : Mem) (base : Nat) (v : BitVec 64) (h : ∀ j, j < 8 → m (base + j) = qbyte v j) : rd64 m base = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hq : i / 8 < 8 := by omega
  have hr : i % 8 < 8 := by omega
  have := getLsbD_rd64 m base (i / 8) (i % 8) hq hr
  rw [show 8 * (i / 8) + i % 8 = i by omega, h (i / 8) hq] at this
  rw [this]
  simp only [qbyte, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hr, decide_true, Bool.true_and]
  congr 1
  omega

theorem rd64_congr (m1 m2 : Mem) (a : Nat) (h : ∀ j, j < 8 → m1 (a + j) = m2 (a + j)) : rd64 m1 a = rd64 m2 a := by
  unfold rd64
  have h0 := h 0 (by omega); have h1 := h 1 (by omega); have h2 := h 2 (by omega); have h3 := h 3 (by omega)
  have h4 := h 4 (by omega); have h5 := h 5 (by omega); have h6 := h 6 (by omega); have h7 := h 7 (by omega)
  simp only [Nat.add_zero] at h0
  rw [h0, h1, h2, h3, h4, h5, h6, h7]

theorem tpCompC_abs (m : Mem) (opAddr p0 N : Nat) (hout : ∀ k, k < N → p0 + 8 * k ≠ opAddr / 8 * 8) :
    tpCompC m opAddr p0 (8 * N) 0 = absRun (qwList m p0 N) (0, 0) := by
  have hsz : (8 * N + 7) / 8 = N := by omega
  unfold tpCompC
  rw [hsz]
  exact tpCompCIter_abs m opAddr N ⟨p0, 0, 0⟩ (fun k hk => hout k hk)

/-- **Forgery at the kernel level.**  Whatever an adversary does to the first `n` quadwords of a region, it can restore the kernel's
value (final sum and operation number, from the canonical start) by choosing the last three quadwords, provided the opcode byte is
outside the region.  The honest image `m0` is arbitrary. -/
theorem forgery_memory (m0 m : Mem) (opAddr p0 n : Nat)
    (hout : ∀ k, k < n + 3 → p0 + 8 * k ≠ opAddr / 8 * 8) :
    ∃ m' : Mem, (∀ a, a < p0 + 8 * n ∨ p0 + 8 * (n + 3) ≤ a → m' a = m a) ∧
      tpCompC m' opAddr p0 (8 * (n + 3)) 0 = tpCompC m0 opAddr p0 (8 * (n + 3)) 0 := by
  have hreach : Reachable (absRun (qwList m0 p0 (n + 3)) (0, 0)) := ⟨_, rfl⟩
  have hs0 : IsOp (absRun (qwList m p0 n) (0, 0)).2 := absRun_isOp _ _ (by simp [IsOp])
  obtain ⟨v1, v2, v3, hv⟩ := forgery_three _ hs0 _ hreach
  let vq : Nat → BitVec 64 := fun j => if j = 0 then v1 else if j = 1 then v2 else v3
  let m' : Mem := fun a => if p0 + 8 * n ≤ a ∧ a < p0 + 8 * (n + 3) then
    qbyte (vq ((a - (p0 + 8 * n)) / 8)) ((a - (p0 + 8 * n)) % 8) else m a
  refine ⟨m', ?_, ?_⟩
  · intro a ha
    simp only [m']
    rw [if_neg (by omega)]
  · have hrd_old : ∀ k, k < n → rd64 m' (p0 + 8 * k) = rd64 m (p0 + 8 * k) := by
      intro k hk
      apply rd64_congr
      intro j hj
      simp only [m']
      rw [if_neg (by omega)]
    have hrd_new : ∀ j, j < 3 → rd64 m' (p0 + 8 * (n + j)) = vq j := by
      intro j hj
      apply rd64_bytes
      intro i hi
      simp only [m']
      rw [if_pos (by omega)]
      have e1 : (p0 + 8 * (n + j) + i - (p0 + 8 * n)) / 8 = j := by omega
      have e2 : (p0 + 8 * (n + j) + i - (p0 + 8 * n)) % 8 = i := by omega
      rw [e1, e2]
    have r0 : rd64 m' (p0 + 8 * n) = v1 := by simpa [vq] using hrd_new 0 (by omega)
    have r1 : rd64 m' (p0 + 8 * (n + 1)) = v2 := by simpa [vq] using hrd_new 1 (by omega)
    have r2 : rd64 m' (p0 + 8 * (n + 2)) = v3 := by simpa [vq] using hrd_new 2 (by omega)
    have hold : qwList m' p0 n = qwList m p0 n := by
      unfold qwList
      apply List.map_congr_left
      intro k hk
      exact hrd_old k (List.mem_range.mp hk)
    have hlist : qwList m' p0 (n + 3) = qwList m p0 n ++ [v1, v2, v3] := by
      rw [qwList_succ, qwList_succ, qwList_succ, hold, r0, r1, r2]
      simp
    rw [tpCompC_abs m' opAddr p0 (n + 3) hout, tpCompC_abs m0 opAddr p0 (n + 3) hout, hlist, absRun_append]
    exact hv


/-- The value of a unit is a function of `tpCompC` on its reset memory. -/
theorem value_eq_of_tpCompC (u : CheckUnit) (M0 M1 : Mem) (hc : u.canon = 0x13) (hal : u.start % 8 = 0)
    (h0 : M0 u.opAddr = 0x13) (h1 : M1 u.opAddr = 0x13)
    (h : tpCompC M1 u.opAddr u.start u.size 0 = tpCompC M0 u.opAddr u.start u.size 0) (hsz : u.size % 8 = 0) :
    u.value M1 = u.value M0 := by
  have hop : IsOp 0 := by simp [IsOp]
  have hK : IsKernelOpcode (0x13 : BitVec 8) := by simp [IsKernelOpcode]
  have e0 : opcodeOf 0 = 0x13 := by decide
  have hs : u.size / 8 = (u.size + 7) / 8 := by omega
  have a0 := static_eq_c M0 u.opAddr u.start u.size 0 (by rw [h0]; exact hK) hop (by rw [h0, e0]) hal
  have a1 := static_eq_c M1 u.opAddr u.start u.size 0 (by rw [h1]; exact hK) hop (by rw [h1, e0]) hal
  simp only [CheckUnit.value, CheckUnit.run, hs]
  obtain ⟨s0, _, m0e⟩ := a0
  obtain ⟨s1, _, m1e⟩ := a1
  rw [m0e, m1e, s0, s1, h]
  simp [wr8]

/-- **Forgery at the unit level (A8 necessity).**  For a unit whose region has at least three quadwords and whose opcode byte lies outside
the region, whatever an adversary does to the earlier quadwords, there are three final quadwords that restore the unit's value (final
sum and opcode byte) to the honest one. -/
theorem forgery_value (u : CheckUnit) (n : Nat) (hsize : u.size = 8 * (n + 3)) (hal : u.start % 8 = 0) (hc : u.canon = 0x13)
    (hout : u.opAddr < u.start ∨ u.start + u.size ≤ u.opAddr) (m0 m : Mem) :
    ∃ m' : Mem, (∀ a, (a < u.start + 8 * n ∨ u.start + 8 * (n + 3) ≤ a) → a ≠ u.opAddr → m' a = m a) ∧
      u.value (u.reset m') = u.value (u.reset m0) := by
  have hq : ∀ k, k < n + 3 → u.start + 8 * k ≠ u.opAddr / 8 * 8 := by
    intro k hk; omega
  obtain ⟨m', hm', ht⟩ := forgery_memory (u.reset m0) (u.reset m) u.opAddr u.start n hq
  have hop' : m' u.opAddr = 0x13 := by
    rw [hm' u.opAddr (by omega)]
    simp [CheckUnit.reset, wr8, hc]
  have hres : u.reset m' = m' := by
    funext a
    by_cases h : a = u.opAddr
    · subst h; simp [CheckUnit.reset, wr8, hop', hc]
    · simp [CheckUnit.reset, wr8, h]
  refine ⟨m', ?_, ?_⟩
  · intro a ha hne
    rw [hm' a ha]
    simp [CheckUnit.reset, wr8, hne]
  · rw [hres]
    exact value_eq_of_tpCompC u (u.reset m0) m' hc hal (by simp [CheckUnit.reset, wr8, hc]) hop'
      (by rw [hsize]; exact ht) (by omega)

end SmcTamper
