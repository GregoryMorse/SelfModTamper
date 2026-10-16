module
public import SmcTamper.Threat.T3full
public import SmcTamper.Harvard.Separation

@[expose] public section

namespace SmcTamper

/-! ## G09: the emulation bound of the cost contract as an instance of the Harvard bound

`Cost.emulLB x` is a contract field. Here it is instantiated: if emulating unit `x` is a Harvard machine that simulates the
unit's von Neumann step, and `ss x` lists distinct sensitive bytes of that step, then every such emulation of elapsed time `e`
(charging `ρ x` per data read on top of the base time `tV x`) satisfies `emulLB x ≤ e`. Which bytes are sensitive for the real
kernel is a hypothesis of the instance (the opcode byte is sensitive in the Level-1 kernel, `Harvard/SplitMemory`); nothing here
says a real CPU or Windows meets the charging hypothesis `hT`. -/

/-- The cost contract whose emulation bound is the Harvard bound. -/
def harvardCost (tV ρ : Nat → Nat) (ss : Nat → List Nat) (kd km : Nat) : Cost :=
  ⟨fun x => tV x + ρ x * (ss x).length, kd, km⟩

theorem harvardCost_emulLB (tV ρ : Nat → Nat) (ss : Nat → List Nat) (kd km x : Nat) :
    (harvardCost tV ρ ss kd km).emulLB x = tV x + ρ x * (ss x).length := rfl

/-- Any Harvard emulation of unit `x` whose time satisfies the charging hypothesis `hT` meets the contract's emulation bound. -/
theorem emul_bound_instance {C S Obs : Type} (H : Harvard C) (V : VonNeumann S) (emb : S → C) (N : Nat)
    (obsH : C → Obs) (obsV : S → Obs) (hsim : Simulates H V emb N obsH obsV) (s : S) (m : Mem)
    (tV ρ : Nat → Nat) (ss : Nat → List Nat) (kd km x : Nat) (hnd : (ss x).Nodup)
    (hss : ∀ a, a ∈ ss x → Sensitive V obsV s m a) (tH : Nat)
    (hT : tV x + ρ x * (H.reads N (emb s) m).length ≤ tH) :
    (harvardCost tV ρ ss kd km).emulLB x ≤ tH :=
  harvard_time_bound H V emb N obsH obsV hsim s m (ss x) hnd hss (ρ x) (tV x) tH hT

/-- With the timing gap of A3, a Harvard emulation of a unit with more than `tau` of Harvard cost is a timing failure of the check. -/
theorem emulated_check_slow (S : Sys) (C : Cost) (hA3 : A3 S C) (x : Nat) (hx : x < S.n) (e : Nat)
    (h : C.emulLB x ≤ e) : (S.unit x).tau < e := by
  obtain ⟨_, h2, _, _⟩ := hA3 x hx
  omega

end SmcTamper
