import EinsteinFull.Frozen.ScaledJointPairing
import Mathlib.Topology.Instances.ENNReal.Lemmas

open MeasureTheory Filter
open scoped NNReal Topology

namespace EinsteinFull
open EinsteinRelation

/-- Meaning of the limiting joint covariance, with actual bilinear spatial
tests and no rate premise. Nonnegative scales R+2 exhaust the required tail. -/
def IsJointCovariance {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q))
    (covariance : Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ) : Prop :=
  ∀ F G : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)),
    Tendsto (fun R : ℝ≥0 =>
      ∫ ω, scaledJointPairing Q ((R : ℝ) + 2) (by positivity) Z F ω *
        scaledJointPairing Q ((R : ℝ) + 2) (by positivity) Z G ω ∂reducedLaw Q)
      atTop (𝓝 (∫ x : Vec d, ∑ a : JointObservationIndex d, ∑ b : JointObservationIndex d,
        F x a * (covariance a b : ℂ) * G x b))

end EinsteinFull
