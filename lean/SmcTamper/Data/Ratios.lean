module
public import SmcTamper.Data.Tables
public import SmcTamper.Contract.Table6

@[expose] public section

namespace SmcTamper

/-! ## Ratios and consistency of the printed numbers (FD)

All ratios are cross-multiplied natural-number inequalities.  `hires t` are the five high-resolution rows (the first five). -/

def hires (t : List Row) : List Row := t.take 5

/-- Sanity: every row of both tables has `min ≤ avg ≤ max`. -/
theorem tables_ordered : (table4 ++ table5).all (fun r => r.smc.ordered && r.non.ordered) = true := by decide

/-- C30: static SMC is `7.9×` slower than static non-SMC in every high-resolution row (`7.85 ≤ ratio < 7.95`). -/
theorem c30_static_ratio : ∀ r ∈ hires table4, 785 * r.non.avg ≤ 100 * r.smc.avg ∧ 100 * r.smc.avg < 795 * r.non.avg := by decide

/-- C32: the faithful non-SMC variant is `90.5×` slower than dynamic SMC in every high-resolution row. -/
theorem c32_dynamic_ratio : ∀ r ∈ hires table5, 9045 * r.smc.avg ≤ 100 * r.non.avg ∧ 100 * r.non.avg < 9055 * r.smc.avg := by decide

/-- C33 / P02: the "about 2.5× faster than the static SMC implementation" matches no ratio of the four RDTSCP averages
(static SMC `8305389`, static non-SMC `1053077`, dynamic SMC `467286`, dynamic non-SMC `42300840`): none of the twelve ordered
ratios lies in `[2.45, 2.55]`; the dynamic SMC is `17.8×` faster than the static SMC. -/
def rdtscpAvgs : List Nat := [8305389, 1053077, 467286, 42300840]

theorem p02_no_ratio_2_5 : ∀ x ∈ rdtscpAvgs, ∀ y ∈ rdtscpAvgs, x ≠ y → ¬ (245 * y ≤ 100 * x ∧ 100 * x ≤ 255 * y) := by decide

theorem p02_17_8 : 1775 * 467286 ≤ 100 * 8305389 ∧ 100 * 8305389 < 1785 * 467286 := by decide

/-- C37 / C09: cycles per `100 ns` unit, the TSC frequency in units of `10 MHz`, lies in `[259.0, 259.3)` in every row of both
tables for the three high-resolution wall-clock timers (so about `2.59 GHz`), and those three timers agree within `6` units. -/
theorem c37_tsc_over_clock : ∀ t ∈ [table4, table5], ∀ i ∈ [2, 3, 4],
    ∀ r ∈ [t.getD 0 ⟨⟨1, 1, 1⟩, ⟨1, 1, 1⟩⟩], ∀ c ∈ [t.getD i ⟨⟨1, 1, 1⟩, ⟨1, 1, 1⟩⟩],
      2590 * c.smc.avg ≤ 10 * r.smc.avg ∧ 10 * r.smc.avg < 2593 * c.smc.avg ∧
      2590 * c.non.avg ≤ 10 * r.non.avg ∧ 10 * r.non.avg < 2593 * c.non.avg := by decide

theorem c09_clocks_agree : ∀ t ∈ [table4, table5], ∀ i ∈ [2, 3, 4], ∀ j ∈ [2, 3, 4],
    ((t.getD i ⟨⟨1, 1, 1⟩, ⟨1, 1, 1⟩⟩).smc.avg + 6 ≥ (t.getD j ⟨⟨1, 1, 1⟩, ⟨1, 1, 1⟩⟩).smc.avg) ∧
    ((t.getD i ⟨⟨1, 1, 1⟩, ⟨1, 1, 1⟩⟩).non.avg + 6 ≥ (t.getD j ⟨⟨1, 1, 1⟩, ⟨1, 1, 1⟩⟩).non.avg) := by decide

/-- C39 / P09: cycles per quadword (`4160` per run): faithful non-SMC `10168`, dynamic SMC `112`; static `253` and `1996`. -/
theorem c39_cycles_per_qword :
    42300840 / 4160 = 10168 ∧ 467286 / 4160 = 112 ∧ 1053077 / 4160 = 253 ∧ 8305389 / 4160 = 1996 := by decide

/-- C31: heavy tail.  In every high-resolution row `avg − min` is less than half of `max − min` (the mass is near the
minimum, the maximum is a rare outlier). -/
theorem c31_heavy_tail : ∀ r ∈ hires table4 ++ hires table5,
    2 * (r.smc.avg - r.smc.min) < r.smc.max - r.smc.min ∧ 2 * (r.non.avg - r.non.min) < r.non.max - r.non.min := by decide

/-- P03: the Table 4 caption says the checksum covered "the entire 220 KB code segment".  `220 KB` is `28160` (binary) or
`27500` (decimal) quadwords, and C12 needs at least `n − 1` clears per run of the naive kernel; Table 6 reports
`8 319.84` per run, below `27 499`, so a 220 KB region is inconsistent with the printed counts, while `0x8200` bytes
(`4160` quadwords, Fig. 5) is consistent. -/
theorem p03_220kb_inconsistent : table6Smc < table6Runs * (28160 - 1) ∧ table6Smc < table6Runs * (27500 - 1) := by
  unfold table6Smc table6Runs; decide

theorem p03_32_5kib : 0x8200 = 33280 ∧ 0x8200 / 1024 = 32 ∧ 0x8200 % 1024 = 512 := by decide

end SmcTamper
