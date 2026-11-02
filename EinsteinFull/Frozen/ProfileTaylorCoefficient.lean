import EinsteinFull.Frozen.GaussianProfile
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

namespace EinsteinFull

/-- The profile Taylor coefficient `h_j = H^(j)(0) / j!` from Section 6. -/
noncomputable def profileTaylorCoefficient (u₀ u₂ γ : ℝ) (j : ℕ) : ℝ :=
  iteratedDeriv j (gaussianProfile u₀ u₂ γ) 0 / (j.factorial : ℝ)

end EinsteinFull
