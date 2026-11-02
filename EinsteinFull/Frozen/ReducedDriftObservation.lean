import EinsteinFull.Frozen.ReducedLaw
import EinsteinFull.Frozen.SmoothEnvironment
import EinsteinRelation.Calculus.Generator
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Complex.Basic

open MeasureTheory

namespace EinsteinFull

open EinsteinRelation

/-- The literal smooth reduced drift `β_i = (1/2) ∑_j ∂_j a_{ji}` at the
origin. The smooth-law domain makes the displayed spatial derivatives actual
derivatives on an almost-everywhere set; no derivative is selected. -/
def IsReducedDriftObservation {d : ℕ} {D : StructuralData d}
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (_hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q)) : Prop :=
  ∀ i, (β i : FieldPair d → ℂ) =ᵐ[reducedLaw Q] fun ω =>
    ((1 / 2 : ℝ) * ∑ j, coordinateDerivative j (fun x => ω.1 x j i) 0 : ℝ)

end EinsteinFull
