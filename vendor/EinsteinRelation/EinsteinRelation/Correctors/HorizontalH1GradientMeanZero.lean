import EinsteinRelation.Correctors.HorizontalGeneratorMeanZero

/-! # Mean zero of the actual horizontal H1 gradient

Source `paper/main.tex:240–248`, with the mean-zero potential gradients at `688–701`. For an
element `f` of the actual horizontal H1 domain, each coordinate of the chosen gradient
`horizontalH1Gradient Q hQ f` is the strong L2 generator of the literal translation group in that
coordinate. The generator has zero expectation on a stationary probability law, by
`HasHorizontalLpDerivative.integral_eq_zero`. This file does not replace `horizontalH1` by a
mean-zero subspace and assumes no core, density, or paper estimate.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

/-- Source main.tex240–248, 688–701: each coordinate of the uniquely chosen horizontal H1 gradient
has zero expectation on a stationary probability law. -/
theorem integral_horizontalH1Gradient_eq_zero {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) (f : horizontalH1 Q hQ) (i : Fin d) :
    (∫ ω, (horizontalH1Gradient Q hQ f i) ω ∂Q) = 0 :=
  HasHorizontalLpDerivative.integral_eq_zero
    (hasHorizontalLpDerivative_horizontalH1Gradient Q hQ f i)

end EinsteinRelation.Correctors
