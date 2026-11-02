import EinsteinFull.Frozen.CorrectorGradient

namespace EinsteinFull

open EinsteinRelation

/-- The actual unforced homogenized coefficient, with column i the expected
canonical corrector flux E[a(e_i + D phi_i)]. -/
noncomputable def homogenizedCoefficient {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) : Mat d :=
  fun j i => Correctors.expectedCorrectorFlux Q i j

end EinsteinFull
