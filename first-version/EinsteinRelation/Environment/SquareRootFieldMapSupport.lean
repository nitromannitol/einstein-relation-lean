import EinsteinRelation.Environment.SquareRootFieldLawSupport

open MeasureTheory
open scoped MatrixOrder

namespace EinsteinRelation

/-- Pointwise square-root dependence is local on the regular physical-field carrier. -/
theorem regularCoefficientSquareRoot_locality {d : ℕ} {Λ : ℝ}
    (ω η : {ω : FieldPair d // IsRegular Λ ω}) (U : Set (Vec d))
    (hlocal : ∀ x ∈ U, ω.1.1 x = η.1.1 x) :
    ∀ x ∈ U, CFC.sqrt (ω.1.1 x) = CFC.sqrt (η.1.1 x) := by
  intro x hx
  rw [hlocal x hx]

/-- Under the actual law, almost every regular environment has the pointwise CFC square root. -/
theorem actualQ_regularCoefficientSquareRoot_spec {d : ℕ} {Λ r₀ : ℝ}
    (hΛ : 1 ≤ Λ) (Q : EnvironmentLaw d Λ r₀) :
    ∀ᵐ ω ∂Q.measure, ∀ x : Vec d,
      CFC.sqrt (ω.1 x) * CFC.sqrt (ω.1 x) = ω.1 x := by
  filter_upwards [Q.regular] with ω hω
  exact fun x => (regularCoefficient_cfcSqrt_spec hΛ ω hω x).1

end EinsteinRelation
