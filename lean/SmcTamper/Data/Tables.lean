module

@[expose] public section

namespace SmcTamper

/-! ## The paper's measurement tables (FD data)

Transcribed from arXiv v1, Tables 4 and 5 (`10 000` runs on an Intel Core i7-9750H, Windows 10).  RDTSC/RDTSCP are in cycles,
`Interrupt Time`, `Perf. Counter` and `Precise UTC` in units of `100 ns`, `Tick Count` and `Multimedia` in milliseconds.
These are *data*: theorems about them state consistency of the printed numbers, never a property of the hardware. -/

structure Stat where
  avg : Nat
  min : Nat
  max : Nat

structure Row where
  smc : Stat
  non : Stat

/-- Table 4 (static SMC kernel), rows in the printed order: RDTSC, RDTSCP, Interrupt Time, Perf. Counter, Precise UTC, Tick Count,
Multimedia. -/
def table4 : List Row :=
  [⟨⟨8305286, 7466370, 17053914⟩, ⟨1052981, 959776, 11039730⟩⟩,
   ⟨⟨8305389, 7466412, 17054428⟩, ⟨1053077, 959834, 11040460⟩⟩,
   ⟨⟨32044, 28806, 65800⟩, ⟨4064, 3704, 42610⟩⟩,
   ⟨⟨32045, 28807, 65802⟩, ⟨4064, 3703, 42617⟩⟩,
   ⟨⟨32045, 28806, 65803⟩, ⟨4065, 3704, 42622⟩⟩,
   ⟨⟨3, 0, 16⟩, ⟨0, 0, 16⟩⟩,
   ⟨⟨3, 1, 7⟩, ⟨0, 0, 4⟩⟩]

/-- Table 5 (dynamic SMC kernel), same row order. -/
def table5 : List Row :=
  [⟨⟨467241, 414132, 2157922⟩, ⟨42300670, 39599882, 74294904⟩⟩,
   ⟨⟨467286, 414188, 2158056⟩, ⟨42300840, 39600010, 74295022⟩⟩,
   ⟨⟨1803, 1598, 8328⟩, ⟨163202, 152779, 286641⟩⟩,
   ⟨⟨1803, 1599, 8327⟩, ⟨163204, 152779, 286644⟩⟩,
   ⟨⟨1803, 1598, 8328⟩, ⟨163206, 152779, 286647⟩⟩,
   ⟨⟨0, 0, 16⟩, ⟨16, 0, 32⟩⟩,
   ⟨⟨0, 0, 2⟩, ⟨16, 15, 29⟩⟩]

def Stat.ordered (s : Stat) : Bool := decide (s.min ≤ s.avg ∧ s.avg ≤ s.max)

end SmcTamper
