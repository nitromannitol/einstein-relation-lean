import EinsteinFull.Frozen.ComplexGaussianProfile
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace EinsteinFull

/-- The literal profile-subtracted correlation E(t,z), with cutoff t>=1. -/
noncomputable def kernelProfileRemainder (d : ℕ) (u₀ u₂ γ : ℝ)
    (K : ℝ → ℂ → ℂ) (t : ℝ) (z : ℂ) : ℂ :=
  K t z - if 1 ≤ t then
    ((t ^ (-1 - (d : ℝ) / 2) : ℝ) : ℂ) *
      complexGaussianProfile u₀ u₂ γ (z * (Real.sqrt t : ℂ)) else 0

end EinsteinFull
