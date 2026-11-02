import EinsteinFull.Frozen.CenteredComplexLp

open MeasureTheory
open scoped NNReal

namespace EinsteinFull

open EinsteinRelation

/-- The clock endpoint `U_c = ζ Π P_t^ζ μ`. -/
noncomputable def clockEndpoint {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (ζ : ℂ)
    (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (μ : Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0) : Lp ℂ 2 (reducedLaw Q) :=
  ζ • centeredComplexLp Q (P t μ)

end EinsteinFull
