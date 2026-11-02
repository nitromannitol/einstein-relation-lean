import EinsteinFull.Frozen.CenteredComplexLp

open MeasureTheory
open scoped NNReal

namespace EinsteinFull

open EinsteinRelation

/-- The forward centered endpoint `U_j = Π P_t^ζ (β_j + ζ a_{ij})`,
where `i` is the force direction. This is a formula, not a chosen endpoint. -/
noncomputable def velocityEndpoint {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i j : Fin d) (ζ : ℂ)
    (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0) :
    Lp ℂ 2 (reducedLaw Q) :=
  centeredComplexLp Q (P t (β j + ζ • a i j))

end EinsteinFull
