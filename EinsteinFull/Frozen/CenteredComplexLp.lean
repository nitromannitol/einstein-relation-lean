import EinsteinFull.Frozen.ReducedLawProbability
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Complex.Basic

open MeasureTheory

namespace EinsteinFull

open EinsteinRelation

/-- The paper's centering `Π f = f - E f` on the actual reduced law. -/
noncomputable def centeredComplexLp {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (f : Lp ℂ 2 (reducedLaw Q)) :
    Lp ℂ 2 (reducedLaw Q) :=
  letI := reducedLaw_probability Q
  f - Lp.const 2 (reducedLaw Q) (∫ ω, f ω ∂reducedLaw Q)

end EinsteinFull
