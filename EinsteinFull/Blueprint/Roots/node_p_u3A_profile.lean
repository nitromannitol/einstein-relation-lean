import EinsteinFull.Frozen.StructuralData
import EinsteinFull.Frozen.SmoothEnvironment
import EinsteinFull.Frozen.ReducedDriftObservation
import EinsteinFull.Frozen.ReducedCoefficientObservation
import EinsteinFull.Frozen.ReducedClockObservation
import EinsteinFull.Frozen.ComplexEnvironmentSemigroup
import EinsteinFull.Frozen.VelocityCorrelation
import EinsteinFull.Frozen.ClockCorrelation
import EinsteinFull.Frozen.JointCovariance
import EinsteinFull.Frozen.ClockGaussianProfile

open MeasureTheory
open scoped NNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Exact statement mirror of `p:profile`; frozen declaration
`EinsteinFull.Frozen.correlation_profile`, source `paper/main.tex:1227–1241`.
No anchor import or conclusion-bearing premise is used. -/
def node_p_u3A_profileStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ α C : ℝ, 0 < α ∧ 0 < C ∧
    (∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
      (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q))
      (covariance : Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → IsJointObservation Q Z →
      IsJointCovariance Q Z covariance →
      (∀ (i : Fin d) (z : ℂ), velocityGaussianProfile hd Q covariance i (-z) =
        velocityGaussianProfile hd Q covariance i z) ∧
      (∀ z : ℂ, clockGaussianProfile hd Q covariance (-z) = clockGaussianProfile hd Q covariance z) ∧
      ∀ t : ℝ≥0, 4 ≤ (t : ℝ) → ∀ ζ : ℂ, ‖ζ‖ * Real.sqrt (t : ℝ) ≤ 2 →
      ∀ P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P → ∀ i : Fin d,
        ‖velocityCorrelation Q ⟨0, by omega⟩ i ζ P β a t -
          (((t : ℝ) ^ (-1 - (d : ℝ) / 2) : ℝ) : ℂ) *
            velocityGaussianProfile hd Q covariance i (ζ * (Real.sqrt (t : ℝ) : ℂ))‖ +
        ‖clockCorrelation Q ⟨0, by omega⟩ ζ P β μ t -
          (((t : ℝ) ^ (-1 - (d : ℝ) / 2) : ℝ) : ℂ) *
            clockGaussianProfile hd Q covariance (ζ * (Real.sqrt (t : ℝ) : ℂ))‖ ≤
          C * (t : ℝ) ^ (-1 - (d : ℝ) / 2 - α) *
            Real.exp (C * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ 2)) ∧
    (∀ C₀ : ℝ, 0 < C₀ → ∃ Cw T₀ : ℝ, 0 < Cw ∧ 4 ≤ T₀ ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
      (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q))
      (covariance : Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → IsJointObservation Q Z →
      IsJointCovariance Q Z covariance →
      ∀ t : ℝ≥0, T₀ ≤ (t : ℝ) → ∀ lam : ℝ,
      |lam| * Real.sqrt (t : ℝ) ≤ C₀ * Real.log (Real.sqrt (t : ℝ)) ^ (1 / 4 : ℝ) →
      ∀ P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ (lam : ℂ) P → ∀ i : Fin d,
        ‖velocityCorrelation Q ⟨0, by omega⟩ i (lam : ℂ) P β a t -
          (((t : ℝ) ^ (-1 - (d : ℝ) / 2) : ℝ) : ℂ) *
            velocityGaussianProfile hd Q covariance i ((lam : ℂ) * (Real.sqrt (t : ℝ) : ℂ))‖ +
        ‖clockCorrelation Q ⟨0, by omega⟩ (lam : ℂ) P β μ t -
          (((t : ℝ) ^ (-1 - (d : ℝ) / 2) : ℝ) : ℂ) *
            clockGaussianProfile hd Q covariance ((lam : ℂ) * (Real.sqrt (t : ℝ) : ℂ))‖ ≤
          Cw * (t : ℝ) ^ (-1 - (d : ℝ) / 2 - α) *
            Real.exp (Cw * (1 + |lam| * Real.sqrt (t : ℝ)) ^ 2))

end EinsteinFull.Blueprint
