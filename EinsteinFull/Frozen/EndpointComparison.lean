import EinsteinFull.Proofs.EndpointComparison
import EinsteinFull.Frozen.StructuralData
import EinsteinFull.Frozen.SmoothEnvironment
import EinsteinFull.Frozen.ReducedDriftObservation
import EinsteinFull.Frozen.ReducedCoefficientObservation
import EinsteinFull.Frozen.ReducedClockObservation
import EinsteinFull.Frozen.ComplexEnvironmentSemigroup
import EinsteinFull.Frozen.ComplexTransposeSemigroup
import EinsteinFull.Frozen.ForcedComparisonError
import EinsteinFull.Frozen.EndpointMomentSum

open MeasureTheory
open scoped NNReal

namespace EinsteinFull.Frozen
open EinsteinRelation

/-- Proposition 6.5, including the forced comparison and endpoint moment consequences. -/
theorem endpoint_comparison (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ gain C : ℝ, 0 < gain ∧ 0 < C ∧
    (    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
      (μ : Lp ℂ 2 (reducedLaw Q))
      (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → IsJointObservation Q Z →
      ∀ R : ℝ, ∀ hR : 0 < R, 2 ≤ R → ∀ z : ℂ, ‖z‖ ≤ 2 →
      ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ (z / (R : ℂ)) P →
      IsComplexTransposeSemigroup Q P Pdag →
      endpointComparisonError hd Q R hR z P Pdag β a μ Z ≤
        C * Real.exp (C * (1 + ‖z‖) ^ 2) *
          (R ^ 2 / 2) ^ (-(1 / 2 + (d : ℝ) / 4) - gain) ∧
      ∀ i : Fin d, forcedComparisonError hd Q R hR z i P β a μ Z ≤
        C * Real.exp (C * (1 + ‖z‖) ^ 2) *
          R ^ (-(d : ℝ) - 2 - 2 * gain)) ∧
    (∀ C₀ : ℝ, 0 < C₀ → ∃ Cw R₀ : ℝ, 0 < Cw ∧ 2 ≤ R₀ ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
      (μ : Lp ℂ 2 (reducedLaw Q))
      (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → IsJointObservation Q Z →
      ∀ R : ℝ, ∀ hR : 0 < R, R₀ ≤ R → ∀ z : ℝ,
      |z| ≤ C₀ * Real.log R ^ (1 / 4 : ℝ) →
      ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ((z : ℂ) / (R : ℂ)) P →
      IsComplexTransposeSemigroup Q P Pdag →
      endpointComparisonError hd Q R hR (z : ℂ) P Pdag β a μ Z ≤
        Cw * Real.exp (Cw * (1 + ‖(z : ℂ)‖) ^ 2) *
          (R ^ 2 / 2) ^ (-(1 / 2 + (d : ℝ) / 4) - gain) ∧
      ∀ i : Fin d, forcedComparisonError hd Q R hR (z : ℂ) i P β a μ Z ≤
        Cw * Real.exp (Cw * (1 + ‖(z : ℂ)‖) ^ 2) *
          R ^ (-(d : ℝ) - 2 - 2 * gain)) ∧
    (∀ p : ℝ, 2 ≤ p → ∃ Cp : ℝ, 0 < Cp ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
      (μ : Lp ℂ 2 (reducedLaw Q))
      (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → IsJointObservation Q Z →
      ∀ lam : ℝ, 0 < |lam| → |lam| ≤ 1 →
      ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ (lam : ℂ) P →
      IsComplexTransposeSemigroup Q P Pdag →
      let T := ((|lam| ^ 2)⁻¹ : ℝ).toNNReal
      (∀ U ∈ endpointCollection Q ⟨0, by omega⟩ (lam : ℂ) P Pdag β a μ T,
        MemLp (U : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)) ∧
      endpointMomentSum hd Q p (lam : ℂ) P Pdag β a μ T ≤
        Cp * |lam| ^ (1 + (d : ℝ) / 2)) := by
  exact EinsteinFull.Proofs.endpoint_comparison d hd D

end EinsteinFull.Frozen
