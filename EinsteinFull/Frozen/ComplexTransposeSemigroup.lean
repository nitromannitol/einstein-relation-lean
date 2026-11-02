import EinsteinFull.Frozen.ReducedLaw
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory
open scoped NNReal

namespace EinsteinFull

open EinsteinRelation

/-- The transpose semigroup under the reduced law, with the paper's bilinear
complex pairing. The forward semigroup is a separate argument; no adjoint with
complex conjugation is substituted. This relation selects no operators. -/
def IsComplexTransposeSemigroup {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)) : Prop :=
  ∀ (t : ℝ≥0) (f g : Lp ℂ 2 (reducedLaw Q)),
    (∫ ω, (P t f) ω * g ω ∂reducedLaw Q) =
      ∫ ω, f ω * (Pdag t g) ω ∂reducedLaw Q

end EinsteinFull
