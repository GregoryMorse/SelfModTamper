module

public section

namespace SmcTamper

/-- Bit `i` of a byte, as a Boolean. -/
@[expose] def bitOf (b : UInt8) (i : Nat) : Bool := (b >>> i.toUInt8) &&& 1 == 1

/-- Number of one bits among the eight bits of a byte. -/
@[expose] def popcount8 (b : UInt8) : Nat := (List.range 8).countP (fun i => bitOf b i)

/-- The x86 parity flag of a byte: set exactly when the number of one bits is even. -/
@[expose] def parityFlag (b : UInt8) : Bool := popcount8 b % 2 == 0

end SmcTamper
