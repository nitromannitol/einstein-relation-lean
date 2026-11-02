import EinsteinFull.Frozen.ComplexEnvironmentSemigroup
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory
open scoped NNReal

namespace EinsteinFull
open EinsteinRelation

/-- The actual finite-time unforced corrector, integral_0^tau P_r^0 beta_i dr,
as a Bochner integral in complex L2, on continuous-orbit families. -/
noncomputable def finiteTimeCorrector {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀)
    (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (_hP : ∀ f : Lp ℂ 2 (reducedLaw Q), Continuous (fun r : ℝ≥0 => P r f))
    (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (τ : ℝ≥0) (i : Fin d) :
    Lp ℂ 2 (reducedLaw Q) :=
  ∫ r in Set.Icc (0 : ℝ) (τ : ℝ), P r.toNNReal (β i)

end EinsteinFull
