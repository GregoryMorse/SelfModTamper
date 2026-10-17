module
public import SmcTamper.Paper
public section
namespace PalomarSMT
/-- Principal results, each from its existing proof in `SmcTamper.Paper`. -/
theorem mathematical_result : SmcTamper.Paper.SecurityTheorem ∧ SmcTamper.Paper.AssumptionsNecessary ∧
    SmcTamper.Paper.MediationTheorem ∧ SmcTamper.Paper.LevelMatrix :=
  ⟨SmcTamper.Paper.security_theorem, SmcTamper.Paper.assumptions_necessary, SmcTamper.Paper.mediation_theorem,
    SmcTamper.Paper.level_matrix⟩
end PalomarSMT
