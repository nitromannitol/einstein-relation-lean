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
import Mathlib.Analysis.Calculus.Deriv.Basic

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Graph node `e:fourier`, `paper/main.tex:1246–1273`.
Second moments of the literal Gaussian tests equal the Fourier integrals with
multiplier ik and the exact frozen anisotropic profiles, for every complex z.
No auxiliary noise or reflection-invariance premise is needed. -/
def node_e_u3A_fourierStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q →
    ∀ (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q))
      (covariance : Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ),
      IsJointObservation Q Z → IsJointCovariance Q Z covariance → ∀ z : ℂ,
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
      let A := homogenizedCoefficient Q
      let v := A.mulVec (unitVector first)
      let density := fun k : Vec d => Complex.exp
        (-((∑ j : Fin d, ∑ l : Fin d, k j * A j l * k l : ℝ) : ℂ) / 2 -
          Complex.I * z * ((∑ j : Fin d, v j * k j : ℝ) : ℂ))
      let cov := fun ν => ∫ x : Vec d,
        ∑ a : JointObservationIndex d, ∑ b : JointObservationIndex d,
          f (.inr true) x a * (covariance a b : ℂ) * f ν x b
      let normalization : ℂ := ((2 * Real.pi) ^ (-(d : ℝ)) : ℝ)
      (∀ i : Fin d,
        cov (.inl i) = normalization * (∫ k : Vec d, density k *
          ((1 / 4 : ℂ) * ∑ j : Fin d, ∑ l : Fin d,
              (k j : ℂ) * (k l : ℂ) * (covariance (.inl (j,first)) (.inl (l,i)) : ℂ))) +
          normalization * (∫ k : Vec d, density k *
            ((1 / 2 : ℂ) * Complex.I * z * ∑ j : Fin d,
              (k j : ℂ) * (covariance (.inl (j,first)) (.inl (first,i)) : ℂ))) ∧
        cov (.inl i) = velocityGaussianProfile hd Q covariance i z) ∧
      cov (.inr false) = normalization * (z / 2) * (∫ k : Vec d,
        density k * (Complex.I * ∑ j : Fin d,
          (k j : ℂ) * (covariance (.inl (j,first)) (.inr ()) : ℂ))) ∧
      cov (.inr false) = clockGaussianProfile hd Q covariance z ∧
      (∀ i, Differentiable ℂ (velocityGaussianProfile hd Q covariance i)) ∧
      Differentiable ℂ (clockGaussianProfile hd Q covariance)

end EinsteinFull.Blueprint
