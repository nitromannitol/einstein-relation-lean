import EinsteinRelation.Correctors.CoefficientProjectionFactorization

/-!
# Variational identification of the coefficient projection

Source: `paper/main.tex:693-698`. Self-adjoint conditional projection
preserves the canonical variational equation when it preserves the actual
potential domain and commutes with the actual coefficient action.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors

/-- Constant vector classes are already coefficient measurable. -/
theorem coefficientProjection_const {d : ℕ} (Q : Measure (FieldPair d))
    [IsFiniteMeasure Q] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (c : E) :
    coefficientProjection Q E (Lp.const 2 Q c) = Lp.const 2 Q c := by
  apply coefficientProjection_eq_self
  exact stronglyMeasurable_const.aestronglyMeasurable.congr
    (Lp.coeFn_const 2 Q c).symm

/-- No uniqueness assumption is needed: the existing variational uniqueness
identifies the projected canonical gradient once invariance is proved. -/
theorem coefficientProjection_canonical_eq_self_of_invariant_domain
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (hdom : ∀ G : correctorPotentialDomain Q,
      coefficientProjection (reducedEnvironmentLaw Q) (EuclideanSpace ℝ (Fin d)) G ∈
        correctorPotentialDomain Q)
    (haction : ∀ G : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q),
      coefficientProjection (reducedEnvironmentLaw Q) (EuclideanSpace ℝ (Fin d))
        (reducedOriginCoefficientAction Q G) =
      reducedOriginCoefficientAction Q
        (coefficientProjection (reducedEnvironmentLaw Q) (EuclideanSpace ℝ (Fin d)) G)) :
    coefficientProjection (reducedEnvironmentLaw Q) (EuclideanSpace ℝ (Fin d))
      (canonicalCorrectorGradient Q i) =
      (canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) := by
  let P := coefficientProjection (reducedEnvironmentLaw Q) (EuclideanSpace ℝ (Fin d))
  let G : correctorPotentialDomain Q :=
    ⟨P (canonicalCorrectorGradient Q i), hdom (canonicalCorrectorGradient Q i)⟩
  have hflux : correctorFluxOfGradient Q i G = P (canonicalCorrectorFlux Q i) := by
    change reducedOriginCoefficientAction Q
      (correctorAffineField Q i + P (canonicalCorrectorGradient Q i)) =
      P (reducedOriginCoefficientAction Q
        (correctorAffineField Q i + (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))))
    rw [haction]
    congr 1
    change correctorAffineField Q i + P (canonicalCorrectorGradient Q i) =
      P (correctorAffineField Q i + (canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)))
    rw [map_add]
    rw [show P (correctorAffineField Q i) = correctorAffineField Q i from
      coefficientProjection_const (reducedEnvironmentLaw Q) (correctorUnitVector i)]
  have hid : G = canonicalCorrectorGradient Q i := by
    apply correctorPotentialDomain_eq_canonical_of_variational
    intro v
    rw [hflux, ← inner_coefficientProjection_left_eq_right]
    exact canonicalCorrectorGradient_variational_domain Q i
      ⟨P v, hdom v⟩
  exact congrArg Subtype.val hid

end EinsteinRelation.Correctors
