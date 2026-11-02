import EinsteinFull.Blueprint.Roots.node_p_u3A_profile
import EinsteinFull.Frozen.IntegratedKernelCoefficient
import EinsteinFull.Frozen.IntegratedKernelCriticalCoefficient
import EinsteinFull.Frozen.CriticalKernelTerm
import EinsteinFull.Frozen.ExpansionModulus
import EinsteinFull.Frozen.ReducedClockRate

open MeasureTheory Filter
open scoped Topology NNReal BigOperators

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Graph node `clock-zero-coefficient`, `paper/main.tex:1302–1302`.
The identically zero force-zero clock correlation and profile give the
zero constant coefficient. Actual fixed-force clock rates retain density bounds. -/
def node_clock_u2D_zero_u2D_coefficientStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ Λ : ℝ, 1 ≤ Λ ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
      (μ : Lp ℂ 2 (reducedLaw Q))
      (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q))
      (covariance : Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → IsJointObservation Q Z →
      IsJointCovariance Q Z covariance →
      ∀ P : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      (∀ z : ℂ, IsComplexEnvironmentSemigroup Q (⟨0, by omega⟩ : Fin d) z (P z)) →
      let first : Fin d := ⟨0, by omega⟩
      (∀ t : ℝ≥0, clockCorrelation Q first 0 (P 0) β μ t = 0) ∧
      clockGaussianProfile hd Q covariance 0 = 0 ∧
      (∫ t in Set.Ici (0 : ℝ),
        (clockCorrelation Q first 0 (P 0) β μ t.toNNReal).re) = 0 ∧
      (let A := homogenizedCoefficient Q
       let p₀ : ℝ := (2 * Real.pi) ^ (-(d : ℝ) / 2) / Real.sqrt A.det
       let γ : ℝ := A first first / 2
       let u₂ : ℝ := p₀ / 2 * covariance (.inl (first, first)) (.inr ())
       let J : ℝ → ℂ → ℂ := fun t z => clockCorrelation Q first z (P z) β μ t.toNNReal
       (∫ t in Set.Ici (0 : ℝ), (kernelProfileRemainder d 0 u₂ γ J t 0).re) +
         2 * profileTaylorCoefficient 0 u₂ γ 0 / (d : ℝ) = 0) ∧
      ∀ (lam : ℝ), lam ≠ 0 → ∀ (Y : QuenchedPathLaws d),
      (∀ᵐ ω ∂Q.measure,
        SolvesMartingaleProblem (reducedGenerator first ω lam) 0 (Y (0, ω))) →
      ∀ η : ℝ, HasReducedClockRate Q Y η →
        Λ⁻¹ ≤ η ∧ η ≤ Λ ∧ ∀ lower upper : ℝ,
          (∀ᵐ ω ∂reducedLaw Q, ∀ x : Vec d, lower ≤ ω.2 x ∧ ω.2 x ≤ upper) →
          lower ≤ η ∧ η ≤ upper

end EinsteinFull.Blueprint
