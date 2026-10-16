module
public import SmcTamper.Contract.UnrolledClears
public import SmcTamper.Contract.StaticClears
public import SmcTamper.Contract.Facts

@[expose] public section

namespace SmcTamper

/-! ## FD: Table 6 against the clear contract

The benchmark protects `0x8200 = 33280` bytes: `4160` quadwords, so the naive kernel runs `4160` iterations and the unrolled
kernel `14` full passes plus a final pass of `16` units (`bench_size_facts`).  Event counts are aggregates over `10 000` runs. -/

def table6Runs : Nat := 10000
def table6C : Nat := 4514
def table6Smc : Nat := 83198361
def table6CLoop : Nat := 20986
def table6SmcLoop : Nat := 4597855
def table6DynLoop : Nat := 4492871

/-- Model upper bound on clears of one run of the unrolled kernel under page granularity: fifteen passes (the final partial
one counted as full), each with at most `2 ⌈W/8⌉` unit-store clears and three intro stores, plus the four tail stores. -/
def runBound (W : Nat) : Nat := 15 * (2 * ((W + 7) / 8) + 3) + 4

/-- Naive SMC: the observed count is consistent with C12 (at least `n − 1 = 4159` clears per run), and equals two events per
iteration up to `1639` of the `83 200 000`. -/
theorem table6_naive : table6Runs * (4160 - 1) ≤ table6Smc ∧ table6Smc + 1639 = 2 * 4160 * table6Runs := by
  unfold table6Runs table6Smc; decide

/-- Unrolled kernels: allowing the `C Loop` count as an upper estimate of unrelated events, the page-granule model's per-run
bound reaches the observation exactly when `W ≥ 105`. -/
theorem table6_loop_page (W : Nat) :
    (table6SmcLoop - table6CLoop ≤ table6Runs * runBound W ∧ table6DynLoop - table6CLoop ≤ table6Runs * runBound W) ↔ 105 ≤ W := by
  unfold table6SmcLoop table6DynLoop table6CLoop table6Runs runBound
  omega

/-- The byte-granule model with `W ≤ 1182` predicts at most `15 · 3 + 4 = 49` clears per run (no unit store clears), far below
the observation: that parameter region is inconsistent with Table 6. -/
theorem table6_loop_byte_inconsistent : table6Runs * (15 * 3 + 4) < table6DynLoop - table6CLoop := by
  unfold table6Runs table6DynLoop table6CLoop; decide

end SmcTamper
