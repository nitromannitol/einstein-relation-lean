import EinsteinRelation.Correctors.CorrectorConditionalStatement
import EinsteinRelation.Correctors.StationarySpatialWeakPotentials
import EinsteinRelation.Correctors.SpatialBallTranslation

/-! Local square integrability of the actual canonical spatial sections,
used in `paper/main.tex:861–883`. -/
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM NormalizedSpatialRepresentativeSupport StationarySpatialRealization

/-- One full-measure event supplies every translated local L² norm of the
canonical gradient. Source: `paper/main.tex:861–883`. -/
theorem ae_canonicalGradient_translated_localL2
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) (y : Point d) :
    ∀ᵐ ω ∂reducedEnvironmentLaw Q, ∀ s : ℝ, 0 < s →
      MemLp (fun x : Vec d => WithLp.toLp 2
        (conditionalCorrectorGradient Q i (WithLp.toLp 2 (x+y.ofLp)) ω)) 2
        (volume.restrict (ball 0 s)) := by
  let g := (canonicalCorrectorGradient Q i :
    Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
  filter_upwards [ae_spatialRealization_memLp_on_all_compacts
    (reducedEnvironmentLaw_stationary Q) g] with ω hω
  have hlocal : ∀ s : ℝ, 0 < s →
      MemLp (fun x : Vec d => g (translate x ω)) 2
        (volume.restrict (ball 0 s)) := by
    intro s hs
    exact (hω (Metric.closedBall 0 s) (isCompact_closedBall _ _)).mono_measure
      (Measure.restrict_mono_set volume (euclideanBall_subset_coordinateClosedBall s hs.le))
  simpa only [conditionalCorrectorGradient, WithLp.ofLp_toLp,
    WithLp.toLp_ofLp, spatialRealization, g] using
    memLp_two_on_euclidean_balls_translation _ hlocal y.ofLp
end EinsteinRelation.Correctors
