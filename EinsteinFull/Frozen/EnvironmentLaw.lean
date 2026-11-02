import EinsteinRelation.Environment.Basic

namespace EinsteinFull

/-- Assumption 1.1, reusing the blueprint's exact joint field-law carrier. -/
abbrev EnvironmentLaw (d : ℕ) (Λ₀ r₀ : ℝ) :=
  EinsteinRelation.EnvironmentLaw d Λ₀ r₀

end EinsteinFull
