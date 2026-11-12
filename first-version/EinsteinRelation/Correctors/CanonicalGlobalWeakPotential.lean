import EinsteinRelation.Correctors.GlobalSpatialWeakPotential
import EinsteinRelation.Correctors.StationarySpatialWeakPotentials
import EinsteinRelation.Correctors.CanonicalVariationalGradientSupport

/-!
# Global scalar weak potentials for canonical gradients

Source: `paper/main.tex:699-704,735-737`. Centered local potentials glue
on the Euclidean-ball exhaustion. The resulting scalar potential has the
literal canonical spatial gradient and is locally square integrable.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger StationarySpatialRealization

/-- A closed stationary gradient has a global weak potential, normalized
by its unit-ball integral, on one common full-measure event. -/
theorem ae_exists_global_spatial_weakPotential_of_closed_gradient
    (hP : BallPoincareEstimate) {d : ℕ} [Fact (2 ≤ d)]
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (G : Lp (EuclideanSpace ℝ (Fin d)) 2 Q)
    (hG : G ∈ stationaryPotentialGradientSubmodule Q hQ) :
    ∀ᵐ ω ∂Q, ∃ u : Vec d → ℝ,
      HasWeakGradient Set.univ u (fun x => (G (translate x ω)).ofLp) ∧
      (∀ R : ℝ, 0 < R → MemLp u 2 (volume.restrict (ball 0 R))) ∧
      (∫ x in ball (0 : Vec d) 1, u x) = 0 := by
  filter_upwards [ae_exists_spatial_weakPotential_of_closed_gradient hP Q hQ G hG,
    ae_spatialRealization_memLp_on_all_compacts hQ G] with ω hpot hlocal
  apply exists_global_weakPotential_of_ball_potentials hP (Fact.out : 2 ≤ d) _ _ hpot
  intro R hR
  apply memLp_pi_iff.mpr
  intro j
  exact ((hlocal (Metric.closedBall 0 R) (isCompact_closedBall _ _)).mono_measure
    (Measure.restrict_mono_set volume
      (euclideanBall_subset_coordinateClosedBall R hR.le))).eval_piLp j

/-- The canonical corrector gradient has actual normalized global scalar
weak potentials, with no extra potential-construction hypothesis. -/
theorem ae_exists_canonical_global_weakPotential
    (hP : BallPoincareEstimate) {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    ∀ᵐ ω ∂reducedEnvironmentLaw Q, ∃ u : Vec d → ℝ,
      HasWeakGradient Set.univ u (fun x => ((canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) (translate x ω)).ofLp) ∧
      (∀ R : ℝ, 0 < R → MemLp u 2 (volume.restrict (ball 0 R))) ∧
      (∫ x in ball (0 : Vec d) 1, u x) = 0 :=
  ae_exists_global_spatial_weakPotential_of_closed_gradient hP
    (reducedEnvironmentLaw Q) (reducedEnvironmentLaw_stationary Q)
    (canonicalCorrectorGradient Q i) (canonicalCorrectorGradient Q i).property

end EinsteinRelation.Correctors
