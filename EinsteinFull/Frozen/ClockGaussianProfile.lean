import EinsteinFull.Frozen.VelocityGaussianProfile

namespace EinsteinFull
open EinsteinRelation

/-- The exact entire clock profile, with the actual commutator-clock cross
covariance C_11 and the same homogenized Gaussian prefactor and decay. -/
noncomputable def clockGaussianProfile {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀)
    (covariance : Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ)
    (z : ℂ) : ℂ :=
  let A := homogenizedCoefficient Q
  let first : Fin d := ⟨0, by omega⟩
  let p₀ : ℝ := (2 * Real.pi) ^ (-(d : ℝ) / 2) / Real.sqrt A.det
  let γ : ℝ := A first first / 2
  let C₁₁ : ℝ := covariance (.inl (first,first)) (.inr ())
  (1 / 2 : ℂ) * (p₀ : ℂ) * (C₁₁ : ℂ) * z ^ 2 *
    Complex.exp (-(γ : ℂ) * z ^ 2)

end EinsteinFull
