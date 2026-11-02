import EinsteinFull.Frozen.HomogenizedGaussianKernel
import EinsteinFull.Frozen.JointObservationIndex

namespace EinsteinFull
open EinsteinRelation

/-- The exact entire velocity profile, with p0, S_i, T_i and gamma taken
from the actual homogenized matrix and limiting joint covariance. -/
noncomputable def velocityGaussianProfile {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀)
    (covariance : Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ)
    (i : Fin d) (z : ℂ) : ℂ :=
  let A := homogenizedCoefficient Q
  let first : Fin d := ⟨0, by omega⟩
  let p₀ : ℝ := (2 * Real.pi) ^ (-(d : ℝ) / 2) / Real.sqrt A.det
  let γ : ℝ := A first first / 2
  let S : ℝ := ∑ j : Fin d, ∑ k : Fin d,
    (A⁻¹) j k * covariance (.inl (j,first)) (.inl (k,i))
  let T : ℝ := covariance (.inl (first,first)) (.inl (first,i))
  (1 / 4 : ℂ) * (p₀ : ℂ) * ((S : ℂ) + (T : ℂ) * z ^ 2) *
    Complex.exp (-(γ : ℂ) * z ^ 2)

end EinsteinFull
