import EinsteinFull.Frozen.ReducedLaw
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Complex.Basic

open MeasureTheory

namespace EinsteinFull

open EinsteinRelation

/-- The clock density of the reduced pair, viewed in complex `L²`. -/
def IsReducedClockObservation {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (μ : Lp ℂ 2 (reducedLaw Q)) : Prop :=
  (μ : FieldPair d → ℂ) =ᵐ[reducedLaw Q] fun ω => (ω.2 0 : ℂ)

end EinsteinFull
