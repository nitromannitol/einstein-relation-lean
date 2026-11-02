import EinsteinFull.Calculus.C2S3PositiveEndpointPast
import EinsteinFull.Calculus.SunaS6KilledEveryStartLocality

open MeasureTheory ProbabilityTheory
open EinsteinRelation EinsteinRelation.Diffusion EinsteinRelation.Regeneration
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal

namespace EinsteinFull

/-- The past-kernel factorization follows from locality of the supplied reduced laws. -/
theorem c10_actual_past_kernel :
    Blueprint.node_app_u3A_factorization_u23_past_u2D_kernelStmt := by
  apply Blueprint.c2_s3_past_kernel_of_requested_locality
  intro d hd Λ₀ r₀ hΛ₀ Q lam l δ hl h0 h1 P K hK v
  dsimp only
  intro ω ω' hω hω' r r' hr hr' hagree y hy
  let U : Set (Vec d) := {z | z (Renewal.forceCoord hd) < v + 3 * (l / lam)}
  have hU : IsOpen U := isOpen_lt (continuous_apply _) continuous_const
  have hyU : y ∈ U := by
    dsimp [U]
    have hR : 0 < l / lam := div_pos hl h0
    linarith
  let : IsMarkovKernel r'.pathLaw := r'.pathLaw_isMarkovKernel
  apply s2_supplied_stopped_locality_of_killed_fdd U hU _ _
  apply s7_supplied_killed_trace_fdd_of_killed_marginals hd (sourceReducedBound Λ₀)
    (one_le_sourceReducedBound hΛ₀) _ _ hω hω' lam h0.le h1 r r' U hU ?_ y hyU
  apply s6_supplied_killed_marginals_of_local_coefficients hd (sourceReducedBound Λ₀)
    (one_le_sourceReducedBound hΛ₀) _ _ hω hω' lam h0.le h1 r r' U hU
  intro z hz
  have hfields := hagree z (le_of_lt hz)
  simp only [zeroPotentialReducedPair_coefficient, reducedCoefficient, clockDensity,
    hfields.1, hfields.2, zeroPotentialReducedPair_potential]
  exact ⟨trivial, trivial⟩

end EinsteinFull
