import EinsteinFull.Frozen.GaussianProfile
import Mathlib.Analysis.Complex.Exponential

namespace EinsteinFull

/-- The entire bilinear continuation of the real Gaussian profile. -/
noncomputable def complexGaussianProfile (u₀ u₂ γ : ℝ) (z : ℂ) : ℂ :=
  ((u₀ : ℂ) + (u₂ : ℂ) * z ^ 2) * Complex.exp (-(γ : ℂ) * z ^ 2)

end EinsteinFull
