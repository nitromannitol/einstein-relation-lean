import EinsteinFull.Frozen.ReducedLaw
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Complex.Basic

open MeasureTheory
open scoped NNReal

namespace EinsteinFull

open EinsteinRelation

/-- The transpose endpoint `U_* = P_t^{ζ,†} β_1`. Identification of the
arguments with the paper's semigroup and drift is supplied separately. -/
noncomputable def transposeEndpoint {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0) : Lp ℂ 2 (reducedLaw Q) :=
  Pdag t (β i)

end EinsteinFull
