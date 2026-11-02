import EinsteinRelation.Correctors.CoefficientProjectionVariational
import EinsteinRelation.Correctors.CoefficientProjectionCoordinates
import EinsteinRelation.Correctors.CoefficientProjectionTranslation
import EinsteinRelation.Correctors.CoefficientActionMeasurability
import EinsteinRelation.Correctors.CoefficientProjectionDomain
import EinsteinRelation.Correctors.HorizontalH1CommutingOperator

/-!
# Coefficient measurability of the actual canonical corrector gradient

Source: `paper/main.tex:693-698`. The coefficient-only conditional
projection commutes with translations and preserves the closed potential
domain. Its self-adjointness and commutation with the coefficient action
preserve the variational equation. Existing variational uniqueness then
identifies the canonical gradient with its coefficient-only projection.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors

/-- The projection preserves the actual closed potential-gradient domain. -/
theorem coefficientProjection_mem_stationaryPotentialGradients {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (G : Lp (EuclideanSpace ℝ (Fin d)) 2 Q)
    (hG : G ∈ stationaryPotentialGradientSubmodule Q hQ) :
    coefficientProjection Q (EuclideanSpace ℝ (Fin d)) G ∈
      stationaryPotentialGradientSubmodule Q hQ := by
  apply coefficientProjection_mem_potentialDomain_of_h1 Q hQ ?_ G hG
  intro f
  obtain ⟨g, _, hg⟩ := horizontalH1_of_commuting_operator Q hQ
    (coefficientProjection Q ℝ) (coefficientProjection_translationLp Q hQ) f
  exact ⟨g, hg⟩

/-- The canonical stationary variational gradient discards no information
under projection onto the actual coefficient observations. -/
theorem coefficientProjection_canonicalCorrectorGradient {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    coefficientProjection (reducedEnvironmentLaw Q) (EuclideanSpace ℝ (Fin d))
      (canonicalCorrectorGradient Q i) =
      (canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) := by
  apply coefficientProjection_canonical_eq_self_of_invariant_domain Q i
  · intro G
    exact coefficientProjection_mem_stationaryPotentialGradients
      (reducedEnvironmentLaw Q) (reducedEnvironmentLaw_stationary Q) G G.property
  · intro G
    exact coefficientProjection_reducedOriginCoefficientAction Q G

/-- A genuine strongly measurable factor of the canonical gradient on
continuous coefficients alone, without the clock coordinate. -/
theorem exists_coefficient_factor_of_canonicalGradient {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    ∃ F : CoefficientField d → EuclideanSpace ℝ (Fin d), StronglyMeasurable F ∧
      (canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) =ᵐ[reducedEnvironmentLaw Q]
          fun ω => F ω.1 := by
  obtain ⟨F, hF, h⟩ := exists_coefficient_factor_of_projection
    (reducedEnvironmentLaw Q) (canonicalCorrectorGradient Q i :
      Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
  rw [coefficientProjection_canonicalCorrectorGradient Q i] at h
  exact ⟨F, hF, h⟩

end EinsteinRelation.Correctors
