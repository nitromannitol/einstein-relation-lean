import EinsteinFull.Blueprint.G1.Draft.SbxCFixedRadiusUniformR07
import EinsteinFull.Blueprint.G1.Draft.SbxCFixedObservationsUniformR08
import EinsteinFull.Blueprint.G1.Draft.SbxCCenteredFirstSlicesUniformR08
import EinsteinFull.Blueprint.G1.Draft.SbxCFirstCycleRemaindersUniformR08
import EinsteinFull.Blueprint.G1.Draft.SbxCFixedRecurrencesUniformR07
import EinsteinFull.Blueprint.G1.Draft.SbxCPhaseRecurrenceUniformR07

/-! Uniform fixed-radius assembly from renewal, factorization and the original remainder. -/
namespace EinsteinFull.Blueprint.SbxCFixedSourceUniformR10

/-- Assemble the uniform fixed-radius estimate from its three source inputs. -/
theorem fixedRadiusUniform_of_source_deps
    (hren : SbxCRenewalUniformR06.renewalUniformStmt)
    (hfact : SbxCFactorizationR01.environmentalFactorizationSmoothStmt)
    (hrem : node_rt_u3A_remainder_u2D_momentStmt) :
    SbxCFixedRadiusUniformR07.fixedRadiusUniformStmtV3 := by
  have hscalar := SbxCFixedRadiusUniformR07.fixedScalarUniform_of_renewal hren
  have hslices := SbxCCenteredFirstSlicesUniformR08.centeredFirstSlicesUniform_of_renewal hren
  have hremainder := SbxCFirstCycleRemaindersUniformR08.firstCycleRemaindersUniform_of_deps hren hrem
  have hrecurrences := SbxCFixedRecurrencesUniformR07.fixed_recurrences_of_smooth_deps hfact
    (SbxCPhaseRecurrenceUniformR07.remainderUniformSmooth_of_all_laws hrem)
  have hobservations := SbxCFixedObservationsUniformR08.fixed_observations_of_uniform_inputs
    hscalar hslices hremainder hrecurrences
  exact SbxCFixedRadiusUniformR07.fixedRadiusUniform_from_scalar_observations
    hscalar hobservations

end EinsteinFull.Blueprint.SbxCFixedSourceUniformR10
