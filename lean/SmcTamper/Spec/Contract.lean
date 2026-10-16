module

@[expose] public section

namespace SmcTamper

/-! ## The clear contract (platform contract item 2, D2)

An *event* is one executed instruction: its address range `[pc, pc + len)` and optionally one store `(address, width)`.
The contract `ClearRule g W κ`: a store triggers a machine clear iff one of the next `W` executed instructions has a byte
in the same `g`-byte granule as a byte of the store (`g = 1` exact bytes, `64` cache line, `4096` page); each clear costs
`κ` cycles on top of an unknown base cost.  The contract is a *definition of the model*, not a claim about hardware:
theorems quantify over `g`, `W`, `κ`. -/

structure Ev where
  pc : Nat
  len : Nat
  store : Option (Nat × Nat)

/-- The granule intervals of the store `[a, a + w)` and the instruction `[p, p + l)` intersect. -/
def granHit (g a w p l : Nat) : Bool := decide (a / g ≤ (p + l - 1) / g ∧ p / g ≤ (a + w - 1) / g)

/-- The store of `e` (if any) causes a clear when one of the next `W` events of `rest` shares a granule with it. -/
def clearsAhead (g W : Nat) (e : Ev) (rest : List Ev) : Bool :=
  match e.store with
  | none => false
  | some (a, w) => (rest.take W).any fun f => granHit g a w f.pc f.len

/-- Clears of a finite trace (events after its end are not seen: this undercounts clears near the end). -/
def clearCount (g W : Nat) : List Ev → Nat
  | [] => 0
  | e :: rest => (if clearsAhead g W e rest then 1 else 0) + clearCount g W rest

/-- The same rule on an infinite (periodic) event stream: does the store at position `t` cause a clear? -/
def streamClear (g W : Nat) (ev : Nat → Ev) (t : Nat) : Bool :=
  match (ev t).store with
  | none => false
  | some (a, w) => (List.range W).any fun d => granHit g a w (ev (t + 1 + d)).pc (ev (t + 1 + d)).len

/-- Time under the contract: an arbitrary base cost plus `κ` per clear. -/
def clearTime (g W κ base : Nat) (tr : List Ev) : Nat := base + κ * clearCount g W tr

end SmcTamper
