import EinsteinFull.Frozen.FiniteTimeCorrector
import EinsteinFull.Frozen.HomogenizedCoefficient

open MeasureTheory
open scoped NNReal

namespace EinsteinFull
open EinsteinRelation

/-- Meaning of the actual finite-time commutator: gradient G is the full
horizontal gradient of phi_i^tau and X_j=(a-A)_{jk}(e_i+G)_k a.e. -/
def IsFiniteTimeCommutator {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀)
    (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : ∀ f : Lp ℂ 2 (reducedLaw Q), Continuous (fun r : ℝ≥0 => P r f))
    (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (τ : ℝ≥0) (i : Fin d)
    (G X : Fin d → Lp ℂ 2 (reducedLaw Q)) : Prop :=
  HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
    (finiteTimeCorrector Q P hP β τ i) G ∧
  ∀ j : Fin d, (X j : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
    fun ω => ∑ k : Fin d, ((ω.1 0 j k - homogenizedCoefficient Q j k : ℝ) : ℂ) *
      (((unitVector i k : ℝ) : ℂ) + G k ω)

end EinsteinFull
