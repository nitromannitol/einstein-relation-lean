import EinsteinRelation.Correctors.CoefficientConditionalProjection

/-!
# Coordinates of the coefficient projection

Source: `paper/main.tex:240-248,693-698`. Conditional expectation commutes
with the genuine Euclidean coordinate projections of the L² gradient.
-/

open MeasureTheory

noncomputable section

namespace EinsteinRelation.Correctors

/-- The scalar coordinate class of the actual Euclidean horizontal gradient. -/
theorem horizontalEuclideanGradient_coordinateLp {d : ℕ}
    (Q : Measure (FieldPair d)) (hQ : IsStationary Q)
    (f : horizontalH1 Q hQ) (i : Fin d) :
    (EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 Q (horizontalEuclideanGradient Q hQ f) =
      horizontalH1Gradient Q hQ f i := by
  apply Lp.ext
  filter_upwards [(EuclideanSpace.proj (𝕜 := ℝ) i).coeFn_compLpL
      (horizontalEuclideanGradient Q hQ f),
    horizontalEuclideanGradient_coordinates Q hQ f i] with ω hp hc
  exact hp.trans hc

/-- Projecting onto coefficient observations commutes with every Euclidean
coordinate, with equality of L² classes rather than chosen point values. -/
theorem coefficientProjection_coordinateLp {d : ℕ} (Q : Measure (FieldPair d))
    [IsFiniteMeasure Q] (G : Lp (EuclideanSpace ℝ (Fin d)) 2 Q) (i : Fin d) :
    (EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 Q
      (coefficientProjection Q (EuclideanSpace ℝ (Fin d)) G) =
    coefficientProjection Q ℝ ((EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 Q G) := by
  apply Lp.ext
  exact Filter.EventuallyEq.symm
    (condExpL2_comp_continuousLinearMap ℝ ℝ (coefficientObservations_le d)
      (EuclideanSpace.proj (𝕜 := ℝ) i) G)

end EinsteinRelation.Correctors
