module
public import SmcTamper.X64.Facts
public import SmcTamper.X64.Step
public import SmcTamper.Bits.Opcode

@[expose] public section

namespace SmcTamper

/-! ## Decode plumbing for `TPComp` run on the modelled ISA

`CodeOk m a0` says that the 46 bytes of `TPComp` (from `MOV RSI,RCX`, listing offset 0x03 of `TP.asm`) sit at
`a0 ..` in `m`, except the opcode byte of the `ADC` (offset 12), which the program itself rewrites. -/

def CodeOk (m : Mem) (a0 : Nat) : Prop :=
  ∀ k, k < 46 → k ≠ 12 → (m (a0 + k)).toNat = tpCompBytes[k]!

theorem tpCompBytes_length : tpCompBytes.length = 46 := by rw [tpCompBytes_listing]; rfl

theorem bytesAt_add (m : Mem) (a n k : Nat) : bytesAt m a (n + k) = bytesAt m a n ++ bytesAt m (a + n) k := by
  simp only [bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro x _
  simp [Nat.add_assoc]

theorem codeOk_wr8 (m : Mem) (a0 : Nat) (b : BitVec 8) (h : CodeOk m a0) : CodeOk (wr8 m (a0 + 12) b) a0 := by
  intro k hk hne
  have := h k hk hne
  simpa [wr8, hne] using this

theorem decode_listing (m : Mem) (a0 off len : Nat) (r : Instr × Nat) (h : CodeOk m a0)
    (hlen : len ≤ 10) (hoff : off + len ≤ 46) (hx : 12 < off ∨ off + len ≤ 12)
    (hd : ∀ t, decodeL (((tpCompBytes.drop off).take len) ++ t) = some r) : decode m (a0 + off) = some r := by
  have e : bytesAt m (a0 + off) 10 = bytesAt m (a0 + off) len ++ bytesAt m (a0 + off + len) (10 - len) := by
    rw [← bytesAt_add]; congr 1; omega
  have e2 : bytesAt m (a0 + off) len = (tpCompBytes.drop off).take len := by
    have hl := tpCompBytes_length
    apply List.ext_getElem
    · simp [bytesAt]; omega
    · intro k h1 h2
      have hk : k < len := by simpa [bytesAt] using h1
      have := h (off + k) (by omega) (by omega)
      simp only [bytesAt, List.getElem_map, List.getElem_range, List.getElem_take, List.getElem_drop]
      rw [show a0 + off + k = a0 + (off + k) by omega, this]
      rw [getElem!_pos tpCompBytes (off + k) (by omega)]
  unfold decode
  rw [e, e2]
  exact hd _
theorem dec_movRR (m : Mem) (a0 : Nat) (h : CodeOk m a0) : decode m (a0 + 0) = some (.movRR 6 1, 3) :=
  decode_listing m a0 0 3 _ h (by omega) (by omega) (by omega) (fun t => by simp [tpCompBytes_listing]; rfl)

theorem dec_leaSib (m : Mem) (a0 : Nat) (h : CodeOk m a0) : decode m (a0 + 3) = some (.leaSib 7 6 2, 4) :=
  decode_listing m a0 3 4 _ h (by omega) (by omega) (by omega) (fun t => by simp [tpCompBytes_listing]; rfl)

theorem dec_xorRR (m : Mem) (a0 : Nat) (h : CodeOk m a0) : decode m (a0 + 7) = some (.alu 6 3 3, 3) :=
  decode_listing m a0 7 3 _ h (by omega) (by omega) (by omega) (fun t => by simp [tpCompBytes_listing]; rfl)

theorem dec_clc (m : Mem) (a0 : Nat) (h : CodeOk m a0) : decode m (a0 + 10) = some (.clc, 1) :=
  decode_listing m a0 10 1 _ h (by omega) (by omega) (by omega) (fun t => by simp [tpCompBytes_listing]; rfl)

theorem dec_sets (m : Mem) (a0 : Nat) (h : CodeOk m a0) : decode m (a0 + 14) = some (.setcc 8 2, 3) :=
  decode_listing m a0 14 3 _ h (by omega) (by omega) (by omega) (fun t => by simp [tpCompBytes_listing]; rfl)

theorem dec_setp (m : Mem) (a0 : Nat) (h : CodeOk m a0) : decode m (a0 + 17) = some (.setcc 10 0, 3) :=
  decode_listing m a0 17 3 _ h (by omega) (by omega) (by omega) (fun t => by simp [tpCompBytes_listing]; rfl)

theorem dec_shlAl (m : Mem) (a0 : Nat) (h : CodeOk m a0) : decode m (a0 + 20) = some (.shlB 0 2, 3) :=
  decode_listing m a0 20 3 _ h (by omega) (by omega) (by omega) (fun t => by simp [tpCompBytes_listing]; rfl)

theorem dec_orDlAl (m : Mem) (a0 : Nat) (h : CodeOk m a0) : decode m (a0 + 23) = some (.orB 2 0, 2) :=
  decode_listing m a0 23 2 _ h (by omega) (by omega) (by omega) (fun t => by simp [tpCompBytes_listing]; rfl)

theorem dec_shlDl (m : Mem) (a0 : Nat) (h : CodeOk m a0) : decode m (a0 + 25) = some (.shlB 2 3, 3) :=
  decode_listing m a0 25 3 _ h (by omega) (by omega) (by omega) (fun t => by simp [tpCompBytes_listing]; rfl)

theorem dec_xorM (m : Mem) (a0 : Nat) (h : CodeOk m a0) : decode m (a0 + 28) = some (.xorMB (BitVec.ofInt 32 (-22)) 2, 6) :=
  decode_listing m a0 28 6 _ h (by omega) (by omega) (by omega) (fun t => by simp [tpCompBytes_listing]; rfl)

theorem dec_leaRsi (m : Mem) (a0 : Nat) (h : CodeOk m a0) : decode m (a0 + 34) = some (.leaD 6 6 8, 4) :=
  decode_listing m a0 34 4 _ h (by omega) (by omega) (by omega) (fun t => by simp [tpCompBytes_listing]; rfl)

theorem dec_cmpRdi (m : Mem) (a0 : Nat) (h : CodeOk m a0) : decode m (a0 + 38) = some (.alu 7 7 6, 3) :=
  decode_listing m a0 38 3 _ h (by omega) (by omega) (by omega) (fun t => by simp [tpCompBytes_listing]; rfl)

theorem dec_jg (m : Mem) (a0 : Nat) (h : CodeOk m a0) : decode m (a0 + 41) = some (.jcc 15 0xE0, 2) :=
  decode_listing m a0 41 2 _ h (by omega) (by omega) (by omega) (fun t => by simp [tpCompBytes_listing]; rfl)

theorem dec_store (m : Mem) (a0 : Nat) (h : CodeOk m a0) : decode m (a0 + 43) = some (.movStore 8 3, 3) :=
  decode_listing m a0 43 3 _ h (by omega) (by omega) (by omega) (fun t => by simp [tpCompBytes_listing]; rfl)

/-- The `ADC`/`SBB`/`XOR`/`CMP` at offset 11: bytes `48 c 1E`, with `c` the (self-modified) opcode byte. -/
theorem dec_alu (m : Mem) (a0 : Nat) (h : CodeOk m a0) (hc : IsKernelOpcode (m (a0 + 12))) :
    decode m (a0 + 11) = some (.aluM (Fin.ofNat 8 (aluField (m (a0 + 12)))) 3 6, 3) := by
  have b0 : (m (a0 + 11)).toNat = 0x48 := by have := h 11 (by omega) (by omega); rw [this, tpCompBytes_listing]; rfl
  have b2 : (m (a0 + 13)).toNat = 0x1E := by have := h 13 (by omega) (by omega); rw [this, tpCompBytes_listing]; rfl
  have e : bytesAt m (a0 + 11) 10 = [0x48, (m (a0 + 12)).toNat, 0x1E] ++ bytesAt m (a0 + 11 + 3) 7 := by
    rw [show (10 : Nat) = 3 + 7 from rfl, bytesAt_add]
    congr 1
    simp [bytesAt, List.range_succ, b0, b2]
  unfold decode
  rw [e]
  rcases hc with h1 | h1 | h1 | h1 <;> rw [h1] <;> rfl

end SmcTamper
