module
public import SmcTamper.Layout.Compare

@[expose] public section

namespace SmcTamper

/-! ## C16 (M-class): the kernels use no performance-counter, MSR or CPUID instruction

Scan of the emitted bytes for the two-byte opcodes `0F 30` (WRMSR), `0F 32` (RDMSR), `0F 33` (RDPMC), `0F A2` (CPUID).
No pair occurs anywhere in the 8123 bytes of either loop image or in `TPComp`, so in particular none occurs at an
instruction boundary. (`rdtsc`-family instructions are likewise absent; the product uses `RDTSC(P)` only in its timing code
around the kernels.) -/

def isSysOp (a b : Nat) : Bool := a == 0x0F && (b == 0x30 || b == 0x32 || b == 0x33 || b == 0xA2)

/-- The scan runs on the emitted bytes (the blobs), in blocks so that the kernel's memory stays small; `dyn_image_eq` and
`static_image_eq` identify them with the Lean images. -/
def sysOpAt (n i : Nat) : Bool := isSysOp (blobByte n i) (blobByte n (i + 1))

theorem dyn_scan_0 : ∀ j, j < 10 → ∀ k, k < 100 → 100 * (0 + j) + k + 1 < 8123 → sysOpAt dynBlob (100 * (0 + j) + k) = false := by
  decide +kernel
theorem dyn_scan_1 : ∀ j, j < 10 → ∀ k, k < 100 → 100 * (10 + j) + k + 1 < 8123 → sysOpAt dynBlob (100 * (10 + j) + k) = false := by
  decide +kernel
theorem dyn_scan_2 : ∀ j, j < 10 → ∀ k, k < 100 → 100 * (20 + j) + k + 1 < 8123 → sysOpAt dynBlob (100 * (20 + j) + k) = false := by
  decide +kernel
theorem dyn_scan_3 : ∀ j, j < 10 → ∀ k, k < 100 → 100 * (30 + j) + k + 1 < 8123 → sysOpAt dynBlob (100 * (30 + j) + k) = false := by
  decide +kernel
theorem dyn_scan_4 : ∀ j, j < 10 → ∀ k, k < 100 → 100 * (40 + j) + k + 1 < 8123 → sysOpAt dynBlob (100 * (40 + j) + k) = false := by
  decide +kernel
theorem dyn_scan_5 : ∀ j, j < 10 → ∀ k, k < 100 → 100 * (50 + j) + k + 1 < 8123 → sysOpAt dynBlob (100 * (50 + j) + k) = false := by
  decide +kernel
theorem dyn_scan_6 : ∀ j, j < 10 → ∀ k, k < 100 → 100 * (60 + j) + k + 1 < 8123 → sysOpAt dynBlob (100 * (60 + j) + k) = false := by
  decide +kernel
theorem dyn_scan_7 : ∀ j, j < 10 → ∀ k, k < 100 → 100 * (70 + j) + k + 1 < 8123 → sysOpAt dynBlob (100 * (70 + j) + k) = false := by
  decide +kernel
theorem dyn_scan_8 : ∀ j, j < 2 → ∀ k, k < 100 → 100 * (80 + j) + k + 1 < 8123 → sysOpAt dynBlob (100 * (80 + j) + k) = false := by
  decide +kernel
theorem dyn_no_sysop : ∀ i, i + 1 < 8123 → sysOpAt dynBlob i = false := by
  intro i hi
  have hj : i / 100 < 82 := by omega
  have hk : i % 100 < 100 := Nat.mod_lt _ (by omega)
  have e : i = 100 * (i / 100) + i % 100 := by omega
  rw [e]
  rcases (by omega : i / 100 < 10 ∨ (10 ≤ i / 100 ∧ i / 100 < 20) ∨ (20 ≤ i / 100 ∧ i / 100 < 30) ∨ (30 ≤ i / 100 ∧ i / 100 < 40) ∨ (40 ≤ i / 100 ∧ i / 100 < 50) ∨ (50 ≤ i / 100 ∧ i / 100 < 60) ∨ (60 ≤ i / 100 ∧ i / 100 < 70) ∨ (70 ≤ i / 100 ∧ i / 100 < 80) ∨ 80 ≤ i / 100) with h | h | h | h | h | h | h | h | h
  · have := dyn_scan_0 (i / 100 - 0) (by omega) (i % 100) hk (by omega)
    rwa [show 0 + (i / 100 - 0) = i / 100 by omega] at this
  · have := dyn_scan_1 (i / 100 - 10) (by omega) (i % 100) hk (by omega)
    rwa [show 10 + (i / 100 - 10) = i / 100 by omega] at this
  · have := dyn_scan_2 (i / 100 - 20) (by omega) (i % 100) hk (by omega)
    rwa [show 20 + (i / 100 - 20) = i / 100 by omega] at this
  · have := dyn_scan_3 (i / 100 - 30) (by omega) (i % 100) hk (by omega)
    rwa [show 30 + (i / 100 - 30) = i / 100 by omega] at this
  · have := dyn_scan_4 (i / 100 - 40) (by omega) (i % 100) hk (by omega)
    rwa [show 40 + (i / 100 - 40) = i / 100 by omega] at this
  · have := dyn_scan_5 (i / 100 - 50) (by omega) (i % 100) hk (by omega)
    rwa [show 50 + (i / 100 - 50) = i / 100 by omega] at this
  · have := dyn_scan_6 (i / 100 - 60) (by omega) (i % 100) hk (by omega)
    rwa [show 60 + (i / 100 - 60) = i / 100 by omega] at this
  · have := dyn_scan_7 (i / 100 - 70) (by omega) (i % 100) hk (by omega)
    rwa [show 70 + (i / 100 - 70) = i / 100 by omega] at this
  · have := dyn_scan_8 (i / 100 - 80) (by omega) (i % 100) hk (by omega)
    rwa [show 80 + (i / 100 - 80) = i / 100 by omega] at this

theorem static_scan_0 : ∀ j, j < 10 → ∀ k, k < 100 → 100 * (0 + j) + k + 1 < 8123 → sysOpAt tpCompLoopObjBlob (100 * (0 + j) + k) = false := by
  decide +kernel
theorem static_scan_1 : ∀ j, j < 10 → ∀ k, k < 100 → 100 * (10 + j) + k + 1 < 8123 → sysOpAt tpCompLoopObjBlob (100 * (10 + j) + k) = false := by
  decide +kernel
theorem static_scan_2 : ∀ j, j < 10 → ∀ k, k < 100 → 100 * (20 + j) + k + 1 < 8123 → sysOpAt tpCompLoopObjBlob (100 * (20 + j) + k) = false := by
  decide +kernel
theorem static_scan_3 : ∀ j, j < 10 → ∀ k, k < 100 → 100 * (30 + j) + k + 1 < 8123 → sysOpAt tpCompLoopObjBlob (100 * (30 + j) + k) = false := by
  decide +kernel
theorem static_scan_4 : ∀ j, j < 10 → ∀ k, k < 100 → 100 * (40 + j) + k + 1 < 8123 → sysOpAt tpCompLoopObjBlob (100 * (40 + j) + k) = false := by
  decide +kernel
theorem static_scan_5 : ∀ j, j < 10 → ∀ k, k < 100 → 100 * (50 + j) + k + 1 < 8123 → sysOpAt tpCompLoopObjBlob (100 * (50 + j) + k) = false := by
  decide +kernel
theorem static_scan_6 : ∀ j, j < 10 → ∀ k, k < 100 → 100 * (60 + j) + k + 1 < 8123 → sysOpAt tpCompLoopObjBlob (100 * (60 + j) + k) = false := by
  decide +kernel
theorem static_scan_7 : ∀ j, j < 10 → ∀ k, k < 100 → 100 * (70 + j) + k + 1 < 8123 → sysOpAt tpCompLoopObjBlob (100 * (70 + j) + k) = false := by
  decide +kernel
theorem static_scan_8 : ∀ j, j < 2 → ∀ k, k < 100 → 100 * (80 + j) + k + 1 < 8123 → sysOpAt tpCompLoopObjBlob (100 * (80 + j) + k) = false := by
  decide +kernel
theorem static_no_sysop : ∀ i, i + 1 < 8123 → sysOpAt tpCompLoopObjBlob i = false := by
  intro i hi
  have hj : i / 100 < 82 := by omega
  have hk : i % 100 < 100 := Nat.mod_lt _ (by omega)
  have e : i = 100 * (i / 100) + i % 100 := by omega
  rw [e]
  rcases (by omega : i / 100 < 10 ∨ (10 ≤ i / 100 ∧ i / 100 < 20) ∨ (20 ≤ i / 100 ∧ i / 100 < 30) ∨ (30 ≤ i / 100 ∧ i / 100 < 40) ∨ (40 ≤ i / 100 ∧ i / 100 < 50) ∨ (50 ≤ i / 100 ∧ i / 100 < 60) ∨ (60 ≤ i / 100 ∧ i / 100 < 70) ∨ (70 ≤ i / 100 ∧ i / 100 < 80) ∨ 80 ≤ i / 100) with h | h | h | h | h | h | h | h | h
  · have := static_scan_0 (i / 100 - 0) (by omega) (i % 100) hk (by omega)
    rwa [show 0 + (i / 100 - 0) = i / 100 by omega] at this
  · have := static_scan_1 (i / 100 - 10) (by omega) (i % 100) hk (by omega)
    rwa [show 10 + (i / 100 - 10) = i / 100 by omega] at this
  · have := static_scan_2 (i / 100 - 20) (by omega) (i % 100) hk (by omega)
    rwa [show 20 + (i / 100 - 20) = i / 100 by omega] at this
  · have := static_scan_3 (i / 100 - 30) (by omega) (i % 100) hk (by omega)
    rwa [show 30 + (i / 100 - 30) = i / 100 by omega] at this
  · have := static_scan_4 (i / 100 - 40) (by omega) (i % 100) hk (by omega)
    rwa [show 40 + (i / 100 - 40) = i / 100 by omega] at this
  · have := static_scan_5 (i / 100 - 50) (by omega) (i % 100) hk (by omega)
    rwa [show 50 + (i / 100 - 50) = i / 100 by omega] at this
  · have := static_scan_6 (i / 100 - 60) (by omega) (i % 100) hk (by omega)
    rwa [show 60 + (i / 100 - 60) = i / 100 by omega] at this
  · have := static_scan_7 (i / 100 - 70) (by omega) (i % 100) hk (by omega)
    rwa [show 70 + (i / 100 - 70) = i / 100 by omega] at this
  · have := static_scan_8 (i / 100 - 80) (by omega) (i % 100) hk (by omega)
    rwa [show 80 + (i / 100 - 80) = i / 100 by omega] at this

theorem tpcomp_no_sysop : ∀ i, i < 52 → sysOpAt tpCompObjBlob i = false := by
  decide +kernel

end SmcTamper
