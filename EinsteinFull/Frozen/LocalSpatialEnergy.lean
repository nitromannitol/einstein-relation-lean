import EinsteinFull.Frozen.ReducedLaw
import EinsteinRelation.External.AKMLocalCorrectors
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Complex.Basic

open scoped NNReal
open MeasureTheory
namespace EinsteinFull
open EinsteinRelation

/-- The literal normalized local energy of the actual stationary gradient
and time derivative. Translation is applied to the fixed representatives,
so the spatial integral is independent of Lp representative choices a.e.
Time is nonnegative and the averaging ball has strictly positive radius. -/
noncomputable def localSpatialEnergy {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (t : ℝ≥0) (ρ : ℝ) (_hρ : 0 < ρ) (x : Vec d)
    (G : Fin d → Lp ℂ 2 (reducedLaw Q)) (V : Lp ℂ 2 (reducedLaw Q))
    (ω : FieldPair d) : ℝ :=
  Real.sqrt (⨍ y in {y : Vec d | euclideanNorm (y - x) < ρ},
    (∑ j : Fin d, ‖G j (translate y ω)‖ ^ 2) + (t : ℝ) * ‖V (translate y ω)‖ ^ 2)

end EinsteinFull
