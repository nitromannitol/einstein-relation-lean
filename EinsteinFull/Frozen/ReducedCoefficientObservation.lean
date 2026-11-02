import EinsteinFull.Frozen.ReducedLaw
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Complex.Basic

open MeasureTheory

namespace EinsteinFull

open EinsteinRelation

/-- The actual reduced matrix entries at the origin as complex `L²` classes. -/
def IsReducedCoefficientObservation {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀)
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) : Prop :=
  ∀ i j, (a i j : FieldPair d → ℂ) =ᵐ[reducedLaw Q] fun ω => (ω.1 0 i j : ℂ)

end EinsteinFull
