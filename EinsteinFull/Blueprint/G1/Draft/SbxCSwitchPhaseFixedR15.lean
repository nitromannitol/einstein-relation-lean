import EinsteinFull.Blueprint.G1.Draft.SbxCFixedSourceUniformR10
import EinsteinFull.Blueprint.G1.Draft.SbxCConditionedCycleUniformR07
import EinsteinFull.Blueprint.G1.Draft.SbxCPhaseUniformR07

/-! Conditional exact graph wrappers for the uniform fixed-radius and phase estimates. -/
namespace EinsteinFull.Blueprint.SbxCSwitchPhaseFixedR15

/-- The original remainder input already supplies the tail-dependent estimate;
    the tails binder is retained for the ordered graph interface. -/
theorem fixedRadius_of_deps
    (hfact : SbxCFactorizationR01.environmentalFactorizationSmoothStmt)
    (hren : SbxCRenewalUniformR06.renewalUniformStmt)
    (hrem : node_rt_u3A_remainder_u2D_momentStmt)
    (_htails : node_app_u3A_regen_u2D_tailsStmt) :
    SbxCFixedRadiusUniformR07.fixedRadiusUniformStmtV3 :=
  SbxCFixedSourceUniformR10.fixedRadiusUniform_of_source_deps hren hfact hrem

/-- The original remainder input already yields the cycle estimate; fixed-radius
    is retained for the ordered graph interface. -/
theorem phase_of_deps
    (hmren : SbxCMRenewalUniformR06.phaseMRenewalSmoothStmt)
    (hren : SbxCRenewalUniformR06.renewalUniformStmt)
    (hrem : node_rt_u3A_remainder_u2D_momentStmt)
    (_hfixed : SbxCFixedRadiusUniformR07.fixedRadiusUniformStmtV3) :
    SbxCPhaseUniformR07.phaseUniformStmt := by
  have hr := SbxCPhaseRecurrenceUniformR07.remainderUniformSmooth_of_all_laws hrem
  exact SbxCPhaseUniformR07.phase_of_uniform_deps
    (SbxCPhaseRecurrenceUniformR07.phase_m_renewal_eq_memLp hmren hr)
    (SbxCConditionedCycleUniformR07.uniform_conditioned_cycle_remainder hren hr)
    hren

end EinsteinFull.Blueprint.SbxCSwitchPhaseFixedR15

