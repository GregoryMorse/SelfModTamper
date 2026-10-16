import SmcTamper.Spec.CModel

/-! Test vectors for the native kernels, generated from the Lean models `tpCompC` and `tpCompCLoop` (`Spec/CModel`).

Output lines (one vector per line, in call order; the native harness replays them in this order, so persistent kernel state
threads exactly as here):
  `V <kind> <seed> <size> <static_sum> <loop_sum>`
sizes avoid multiples of 1184 bytes (148 qwords): the unrolled asm kernels do not support them (CODE_FIXES L07).
kinds: `R` pseudo-random qwords (xorshift64 from `seed`), `Z` zeros, `F` all bytes 0xFF, `H` every qword 0x8000000000000000.
`static_sum` is the sum of the single-site kernel `TPComp` / `TPCompC`, `loop_sum` the sum of the unrolled kernel `TPCompLoop` /
`TPCompCLoop` / the AsmJit kernel, each started from its canonical state and threaded across the vectors in order. -/

open SmcTamper

def xorshift (x : UInt64) : UInt64 :=
  let x := x ^^^ (x <<< 13)
  let x := x ^^^ (x >>> 7)
  x ^^^ (x <<< 17)

def qwords (kind : Char) (seed : Nat) (n : Nat) : Array UInt64 := Id.run do
  let mut st : UInt64 := (UInt64.ofNat seed) * 0x9E3779B97F4A7C15 + 1
  let mut out := #[]
  for _ in [0:n] do
    st := xorshift st
    out := out.push (match kind with
      | 'Z' => 0
      | 'F' => 0xFFFFFFFFFFFFFFFF
      | 'H' => 0x8000000000000000
      | _ => st)
  return out

def memOf (qs : Array UInt64) : Mem := fun a =>
  let i := a / 8
  if h : i < qs.size then BitVec.ofNat 8 ((qs[i].toNat >>> (8 * (a % 8))) % 256) else 0

def vectors : List (Char × Nat × Nat) :=
  let sizes := [8, 16, 24, 64, 128, 2376, 2384, 2392, 4744, 4752, 7112, 9480, 16000]
  (List.range 26).map (fun i => ('R', i + 1, sizes[i % sizes.length]!)) ++
  [('Z', 0, 64), ('Z', 0, 2376), ('Z', 0, 4744), ('F', 0, 64), ('F', 0, 2376), ('F', 0, 4744),
   ('H', 0, 64), ('H', 0, 2376), ('H', 0, 4744), ('H', 0, 8)]

def run : IO Unit := do
  let mut op : Nat := 0
  let mut ops : Nat → Nat := fun _ => 0
  for (kind, seed, size) in vectors do
    let qs := qwords kind seed (size / 8)
    let m := memOf qs
    let (s1, op') := tpCompC m (1 <<< 40) 0 size op
    op := op'
    let c := tpCompCLoop m (1 <<< 40) 0 size ops
    ops := c.op
    IO.println s!"V {kind} {seed} {size} {s1.toNat} {c.sum.toNat}"

#eval run
