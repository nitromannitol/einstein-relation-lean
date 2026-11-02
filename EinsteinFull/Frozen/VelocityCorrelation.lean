import EinsteinFull.Frozen.ReducedLaw
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Complex.Basic

open MeasureTheory
open scoped NNReal

namespace EinsteinFull

open EinsteinRelation

/-- The literal bilinear velocity correlation `K_j(t,ζ)`. All factors are
`L²` classes, so the pairing is independent of representatives. -/
noncomputable def velocityCorrelation {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i j : Fin d) (ζ : ℂ)
    (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0) : ℂ :=
  ∫ ω, β i ω * (P t (β j + ζ • a i j)) ω ∂reducedLaw Q

end EinsteinFull
