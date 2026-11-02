import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace EinsteinFull

/-- The real Gaussian profile used in Proposition 6.7. -/
noncomputable def gaussianProfile (u₀ u₂ γ : ℝ) (z : ℝ) : ℝ :=
  (u₀ + u₂ * z ^ 2) * Real.exp (-γ * z ^ 2)

end EinsteinFull
