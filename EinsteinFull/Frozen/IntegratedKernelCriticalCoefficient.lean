import EinsteinFull.Frozen.ProfileFinitePart

namespace EinsteinFull

/-- The prescribed coefficient chi of the critical kernel term T_d. -/
noncomputable def integratedKernelCriticalCoefficient (d : ℕ) (u₀ u₂ γ : ℝ)
    (hγ : 0 < γ) : ℝ :=
  if Even d then 2 * profileTaylorCoefficient u₀ u₂ γ d
  else 2 * profileFinitePart d u₀ u₂ γ hγ

end EinsteinFull
