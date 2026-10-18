module
public import SmcTamper.Threat.Closure

@[expose] public section

namespace SmcTamper

/-! ## T1: security against adversaries within the assumptions

The proof has three parts: a persistent modification is read by an intact unit (closure), the intact unit's check either shows a
value mismatch (A8) or was emulated or debugged, which costs more than the threshold (A3, A5), and `k` such checks in a row raise
the alarm (A6). -/

theorem Sched.ck_ge (n : Nat) (tl : Nat → TEv) (sch : Sched n tl) (x : Nat) : ∀ m, m ≤ sch.ck x m := by
  intro m
  induction m with
  | zero => exact Nat.zero_le _
  | succ m ih => have := sch.incr x m; omega

/-- The first check of `x` after stream index `i`. -/
theorem first_check_after (n : Nat) (tl : Nat → TEv) (sch : Sched n tl) (x i : Nat) :
    ∃ m0, i < sch.ck x m0 ∧ (m0 = 0 ∨ sch.ck x (m0 - 1) ≤ i) := by
  have key : ∀ m, i < sch.ck x m → ∃ m0, i < sch.ck x m0 ∧ (m0 = 0 ∨ sch.ck x (m0 - 1) ≤ i) := by
    intro m
    induction m with
    | zero => intro h; exact ⟨0, h, Or.inl rfl⟩
    | succ m ih =>
      intro h
      by_cases hle : sch.ck x m ≤ i
      · exact ⟨m + 1, h, Or.inr (by simpa using hle)⟩
      · exact ih (by omega)
  exact key (i + 1) (by have := Sched.ck_ge _ tl sch x (i + 1); omega)

/-- Check events of an intact unit are honest, or their reading exceeds the threshold. -/

theorem check_cases (S : Sys) (C : Cost) (l : Level) (t : TimerSrc) (tl : Nat → TEv) (sch : Sched S.n tl)
    (hwf : WF S C l t tl) (hA : Assumptions S C tl sch) (y : Nat) (hy : y < S.n) (hint : Intact S tl y)
    (idx : Nat) (p : CheckPath) (e r : Nat) (hev : tl idx = TEv.check y p e r) :
    (∃ e' r', tl idx = TEv.check y .honest e' r') ∨ timeFailAt S tl idx y := by
  have h3 := hA.a3 y hy
  have hr := hA.a5 idx y p e r hev
  have hc := hwf.cost idx
  rw [hev] at hc
  cases p with
  | honest => exact Or.inl ⟨e, r, hev⟩
  | emulated =>
    right
    refine ⟨.emulated, e, r, hev, ?_⟩
    simp only [Cost.admits] at hc
    omega
  | forged =>
    right
    refine ⟨.forged, e, r, hev, ?_⟩
    simp only [Cost.admits] at hc
    omega
  | neutral =>
    exfalso
    obtain ⟨a, hca, hoa, hne⟩ := hwf.neutralMod idx y e r hev
    exact hne (intact_code_orig S tl hA.a1 hA.a4 y hint a hca hoa idx)
  | mediated med =>
    exfalso
    have := hwf.medSplit idx y med e r hev
    rw [hA.a1 idx] at this
    cases this

/-- **Core of T1.**  A modifying write to a byte of an intact unit's region raises an effective alarm. -/
theorem core_alarm (S : Sys) (C : Cost) (l : Level) (t : TimerSrc) (tl : Nat → TEv) (sch : Sched S.n tl)
    (hwf : WF S C l t tl) (hA : Assumptions S C tl sch) (y : Nat) (hy : y < S.n) (hint : Intact S tl y)
    (i c : Nat) (b : BitVec 8) (hw : tl i = TEv.write c b) (hprot : S.prot c) (hops : ¬ S.ops c) (hb : b ≠ S.I0 c)
    (hreg : S.inRegion y c) : Alarm S tl sch := by
  obtain ⟨m0, hm1, hm2⟩ := first_check_after _ tl sch y i
  have hpers := hA.a6.2 i c b y m0 hw hprot hops hb hy hreg hm1 hm2
  have hresp : RespIntact S tl y := by
    refine ⟨(hA.a7 y hy).1, ?_⟩
    intro n a ha
    obtain ⟨hca, hoa⟩ := (hA.a7 y hy).2 a ha
    exact intact_code_orig S tl hA.a1 hA.a4 y hint a hca hoa n
  refine ⟨y, hy, hresp, ?_⟩
  by_cases hh : ∃ j, j < S.k ∧ ∃ e r, tl (sch.ck y (m0 + j)) = TEv.check y .honest e r
  · left
    obtain ⟨j, hj, e, r, hev⟩ := hh
    refine ⟨m0 + j, ?_⟩
    have hnot := hA.a8 y (m0 + j) e r hy hev ⟨c, hreg, hops, hpers j hj⟩
    exact ⟨.honest, e, r, hev, hnot⟩
  · right
    refine ⟨hA.a6.1, m0, ?_⟩
    intro j hj
    obtain ⟨p, e, r, hev⟩ := sch.isChk y (m0 + j) hy
    rcases check_cases S C l t tl sch hwf hA y hy hint (sch.ck y (m0 + j)) p e r hev with ⟨e', r', h'⟩ | hf
    · exact absurd ⟨j, hj, e', r', h'⟩ hh
    · exact hf

/-- **T1 (security).**  Under the cost contract and A1–A8, the adversary never wins: every executed modification of a protected non-opcode
byte is accompanied by an effective alarm. -/
theorem security (S : Sys) (C : Cost) (l : Level) (t : TimerSrc) (tl : Nat → TEv) (sch : Sched S.n tl)
    (hwf : WF S C l t tl) (hA : Assumptions S C tl sch) : ¬ Wins S tl sch := by
  intro ⟨⟨j, a, hexec, hprot, hops, hne⟩, hnoalarm⟩
  apply hnoalarm
  obtain ⟨i, b, _, hw, hb⟩ := last_write S tl hA.a1 hA.a4 a j hne
  obtain ⟨x, hx, hreg⟩ := hA.a2cov a hprot
  by_cases hint : Intact S tl x
  · exact core_alarm S C l t tl sch hwf hA x hx hint i a b hw hprot hops hb hreg
  · have hmod : ModWrite S tl x := Classical.byContradiction (fun h => hint h)
    obtain ⟨v, hv, hvint⟩ := hA.a2intact
    have hreach := hA.a2conn v x hv hx
    obtain ⟨y, u', i', c, b', hy, hu', hyint, hw', hops', hb', hreg', hcode⟩ := closure_detect S tl v hvint x hreach hmod
    exact core_alarm S C l t tl sch hwf hA y hy hyint i' c b' hw' (hA.a2code u' hu' c hcode) hops' hb' hreg'

end SmcTamper
