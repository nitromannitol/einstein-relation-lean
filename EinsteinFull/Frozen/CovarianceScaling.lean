import EinsteinFull.Proofs.CovarianceScaling
import EinsteinFull.Frozen.StructuralData
import EinsteinFull.Frozen.SmoothEnvironment
import EinsteinFull.Frozen.ScaledJointPairing
import EinsteinFull.Frozen.SchwartzTestNorm
import Mathlib.LinearAlgebra.Matrix.PosDef

open MeasureTheory

namespace EinsteinFull.Frozen

open EinsteinRelation

/-- Proposition 5.1: a law-dependent positive semidefinite covariance, with a
power rate uniform in the structural class and the same bilinear complex tests. -/
theorem covariance_scaling (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (N : ℕ) (hN : 2 * d + 10 < N) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q →
    ∃ covariance : Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ,
      covariance.PosSemidef ∧
      (∀ ξ : EuclideanSpace ℝ (JointObservationIndex d),
        ‖WithLp.toLp 2 (covariance.mulVec (WithLp.ofLp ξ))‖ ≤ C * ‖ξ‖) ∧
      ∀ Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q),
        IsJointObservation Q Z → ∀ R : ℝ, ∀ hR : 2 ≤ R,
      ∀ F G : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)),
        ‖(∫ ω, scaledJointPairing Q R (by linarith) Z F ω *
          scaledJointPairing Q R (by linarith) Z G ω ∂reducedLaw Q) -
          ∫ x : Vec d, ∑ a : JointObservationIndex d, ∑ b : JointObservationIndex d,
            F x a * (covariance a b : ℂ) * G x b‖ ≤
        C * schwartzTestNorm N F * schwartzTestNorm N G * R ^ (-ε) := by
  exact EinsteinFull.Proofs.covariance_scaling d hd D N hN

end EinsteinFull.Frozen
