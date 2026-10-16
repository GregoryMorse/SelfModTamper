module
public import SmcTamper.Spec.CModel
public import SmcTamper.Spec.Layout

@[expose] public section

namespace SmcTamper

/-! ## C11 and C23: the monitored sites of the unrolled kernel

The C emulation `tpCompCLoop` consults a table (`adjustEntries base`) of the qwords that contain one of the kernel's opcode bytes.
The table is a translate of a fixed one when the code is generated at another (8-aligned-shift) address (`adjustEntries_shift`: the monitored
addresses are `base + const`, "contextual" in the sense that they depend on where the code was generated), and it has one distinct qword
per unit, so its size is the unroll depth (`sites_nodup`, `sites_length`, `adjust_keys_nodup`).  How much harder this makes a faithful
emulator is not a theorem; the proved statement is that the tracked state has `D` independent sites for depth `D`. -/

theorem nodup_map_range (f : Nat → Nat) (D : Nat) (h : ∀ i j, i < j → j < D → f i ≠ f j) :
    (List.map f (List.range D)).Nodup := by
  unfold List.Nodup
  rw [List.pairwise_map]
  exact List.pairwise_lt_range.imp_of_mem (fun {a b} ha hb hab => h a b hab (by simpa using hb))

/-- The qwords containing the opcode bytes of units `0 .. D - 1` of an unrolled kernel at `base`, in a layout with first site at offset `c`
and stride `27` (one unit). -/
def sites (c base D : Nat) : List Nat := (List.range D).map (fun i => (base + c + 27 * i) / 8 * 8)

theorem sites_length (c base D : Nat) : (sites c base D).length = D := by simp [sites]

theorem sites_nodup (c base D : Nat) : (sites c base D).Nodup := by
  unfold sites
  apply nodup_map_range
  intro i j hij hj
  omega

/-- Strictly more sites for a deeper unrolling: the tracked state grows with the depth. -/
theorem sites_grow (c base D : Nat) : (sites c base (D + 1)).length = (sites c base D).length + 1 := by
  simp [sites_length]

/-- The table of the C emulation has one entry per unit, and no two units share a qword. -/
theorem adjust_keys_nodup (base : Nat) : ((adjustEntries base).map (fun e => e.1)).Nodup := by
  unfold adjustEntries
  rw [List.map_append, List.map_map, List.map_map, List.nodup_append]
  refine ⟨?_, ?_, ?_⟩
  · apply nodup_map_range
    intro i j hij hj
    simp only [Function.comp]
    omega
  · apply nodup_map_range
    intro i j hij hj
    simp only [Function.comp]
    omega
  · intro a ha b hb hab
    simp only [List.mem_map, List.mem_range, Function.comp] at ha hb
    obtain ⟨i, hi, rfl⟩ := ha
    obtain ⟨j, hj, rfl⟩ := hb
    omega

theorem adjust_length (base : Nat) : (adjustEntries base).length = 296 := by
  simp [adjustEntries]

/-- C11: the monitored addresses move with the base address: shifting the code by a multiple of 8 shifts every entry. -/
theorem adjustEntries_shift (base t : Nat) :
    adjustEntries (base + 8 * t) = (adjustEntries base).map (fun e => (e.1 + 8 * t, e.2.1, e.2.2)) := by
  unfold adjustEntries
  rw [List.map_append, List.map_map, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro i _
    show (_, _, _) = (_, _, _)
    refine Prod.ext ?_ (Prod.ext ?_ rfl) <;> dsimp only <;> omega
  · apply List.map_congr_left
    intro i _
    show (_, _, _) = (_, _, _)
    refine Prod.ext ?_ (Prod.ext ?_ rfl) <;> dsimp only <;> omega

end SmcTamper
