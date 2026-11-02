import EinsteinFull.Frozen.StructuralData
import EinsteinFull.Frozen.SmoothEnvironment
import EinsteinFull.Frozen.ReducedDriftObservation
import EinsteinFull.Frozen.ReducedCoefficientObservation
import EinsteinFull.Frozen.ReducedClockObservation
import EinsteinFull.Frozen.ComplexEnvironmentSemigroup
import EinsteinFull.Frozen.ComplexTransposeSemigroup
import EinsteinFull.Frozen.EndpointWeakFlux
import EinsteinFull.Frozen.GaussianAverage
import EinsteinFull.Frozen.ModelClockEndpoint
import EinsteinFull.Frozen.ModelVelocityEndpoint
import EinsteinFull.Frozen.ModelTransposeEndpoint
import EinsteinFull.Frozen.JointCovariance
import EinsteinFull.Frozen.SchwartzTestNorm
import EinsteinFull.Frozen.VelocityGaussianProfile
import EinsteinFull.Frozen.ClockGaussianProfile
import EinsteinFull.Frozen.VelocityCorrelation
import EinsteinFull.Frozen.ClockCorrelation
import Mathlib.Analysis.Calculus.Deriv.Basic

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Graph node `p:profile#static-comparison`, `paper/main.tex:1244`.
Literal Gaussian Schwartz tests, their exact model realization and the static
and dynamical covariance errors. The final time gain is half the minimum of
the positive static and bridge scale gains, before choosing the law. -/
def node_p_u3A_profile_u23_static_u2D_comparisonStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∀ (N : ℕ), 2 * d + 10 < N →
    ∃ εcov εbridge C : ℝ, 0 < εcov ∧ 0 < εbridge ∧ 0 < C ∧
    ∀ C₀ : ℝ, 0 < C₀ → ∃ Cw R₀ : ℝ, 0 < Cw ∧ 2 ≤ R₀ ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q →
    ∃ covariance : Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ,
    ∀ Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q), IsJointObservation Q Z →
      IsJointCovariance Q Z covariance ∧
      ∀ z : ℂ,
      let first : Fin d := ⟨0, by omega⟩
      let kernel := fun (w : ℂ) => homogenizedGaussianKernel Q first (1 / 2) (by norm_num) w
      let kernelDeriv := fun (w : ℂ) (j : Fin d) (x : Vec d) =>
        iteratedFDeriv ℝ 1 (kernel w) (-x) (fun _ => unitVector j)
      let f := fun (ν : EndpointIndex d) (x : Vec d) (a : JointObservationIndex d) =>
        match ν, a with
        | .inr true, .inl (j,k) => if k = first then (1 / 2 : ℂ) * kernelDeriv z j x else 0
        | .inl i, .inl (j,k) => if k = i then
            (1 / 2 : ℂ) * kernelDeriv (-z) j x +
              (if j = first then z * kernel z x else 0) else 0
        | .inr false, .inr () => z * kernel z x
        | _, _ => 0
      ∃ F : EndpointIndex d → SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)),
        (∀ ν x a, F ν x a = f ν x a) ∧
        (∀ ν, schwartzTestNorm N (F ν) ≤ C * Real.exp (C * (1 + ‖z‖) ^ 2)) ∧
        ∀ (R : ℝ) (hR : 0 < R), 2 ≤ R →
          let T : ℝ := R ^ 2 / 2
          let hT : 0 < T := by positivity
          let ζ := z / (R : ℂ)
          let model := fun ν : EndpointIndex d => match ν with
            | .inl i => modelVelocityEndpoint hd Q Z i T hT ζ
            | .inr true => modelTransposeEndpoint hd Q Z T hT ζ
            | .inr false => modelClockEndpoint hd Q Z T hT ζ
          let cov := fun ν => ∫ x : Vec d,
            ∑ a : JointObservationIndex d, ∑ b : JointObservationIndex d,
              F (.inr true) x a * (covariance a b : ℂ) * F ν x b
          (∀ ν, model ν = ((R ^ (-1 - (d : ℝ) / 2) : ℝ) : ℂ) •
            scaledJointPairing Q R hR Z (F ν)) ∧
          (∀ ν, ‖(∫ ω, model (.inr true) ω * model ν ω ∂reducedLaw Q) -
            ((R ^ (-(d : ℝ) - 2) : ℝ) : ℂ) * cov ν‖ ≤
              C * Real.exp (C * (1 + ‖z‖) ^ 2) * R ^ (-(d : ℝ) - 2 - εcov)) ∧
          ∀ (β : Fin d → Lp ℂ 2 (reducedLaw Q))
            (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
            (hQ : HasSmoothBounds D Q),
            IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
            IsReducedClockObservation Q μ →
          ∀ P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
            IsComplexEnvironmentSemigroup Q first ζ P →
          ∀ i : Fin d,
            let error := ‖velocityCorrelation Q first i ζ P β a (R ^ 2).toNNReal -
                ((R ^ (-(d : ℝ) - 2) : ℝ) : ℂ) * cov (.inl i)‖ +
              ‖clockCorrelation Q first ζ P β μ (R ^ 2).toNNReal -
                ((R ^ (-(d : ℝ) - 2) : ℝ) : ℂ) * cov (.inr false)‖
            (‖z‖ ≤ 2 → error ≤ C * Real.exp (C * (1 + ‖z‖) ^ 2) *
              R ^ (-(d : ℝ) - 2 - min εcov εbridge)) ∧
            (R₀ ≤ R → (∃ x : ℝ, z = (x : ℂ) ∧
              |x| ≤ C₀ * Real.log R ^ (1 / 4 : ℝ)) →
              error ≤ Cw * Real.exp (Cw * (1 + ‖z‖) ^ 2) *
                R ^ (-(d : ℝ) - 2 - min εcov εbridge))

end EinsteinFull.Blueprint
