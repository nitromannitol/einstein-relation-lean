import EinsteinRelation.Environment.Basic

open MeasureTheory

namespace EinsteinRelation

/-- The source environment setting for Theorem 1.2 on the joint physical
coefficient/potential law. The spatial regularity conditions hold almost surely;
stationarity and finite range are conditions on the joint law. -/
def EnvironmentAdmissible {d : ℕ} (Λ₀ r₀ : ℝ)
    (Q : Measure (FieldPair d)) : Prop :=
  2 ≤ d ∧
  1 ≤ Λ₀ ∧
  1 ≤ r₀ ∧
  IsProbabilityMeasure Q ∧
  (∀ᵐ ω ∂Q,
    (∀ x : Vec d,
      (ω.1 x).transpose = ω.1 x ∧
      ∀ ξ : Vec d,
        Λ₀⁻¹ * euclideanSq ξ ≤ dot ξ ((ω.1 x).mulVec ξ) ∧
        dot ξ ((ω.1 x).mulVec ξ) ≤ Λ₀ * euclideanSq ξ) ∧
    (∀ x : Vec d, |ω.2 x| ≤ Λ₀) ∧
    (∀ x y ξ : Vec d,
      euclideanNorm ((ω.1 x - ω.1 y).mulVec ξ) ≤
        Λ₀ * euclideanNorm (x - y) * euclideanNorm ξ) ∧
    (∀ x y : Vec d,
      |ω.2 x - ω.2 y| ≤ Λ₀ * euclideanNorm (x - y))) ∧
  (∀ x : Vec d, Measure.map (translate x) Q = Q) ∧
  (∀ U W : Set (Vec d),
    MeasurableSet U → MeasurableSet W →
    (∃ s : ℝ, r₀ < s ∧ ∀ x ∈ U, ∀ y ∈ W, s ≤ euclideanNorm (x - y)) →
    ProbabilityTheory.Indep (localSigma U) (localSigma W) Q)

end EinsteinRelation
