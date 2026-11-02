import EinsteinRelation.External.AKMLocalCorrectors
import Mathlib.MeasureTheory.Integral.Prod

/-! # Temporal endpoints of genuine weak parabolic cylinders

Source: `paper/main.tex:788–796,834–845`. The source regularity estimates
use cylinders closed at their final time. Energy membership and the weak
PDE are invariant under adding that single time slice.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Source: `paper/main.tex:788–796,834–845`. Adding the final time
slice preserves the complete weak energy-cylinder predicate. -/
theorem parabolicSolution_Ioc_of_Ioo {d : ℕ} {K a b : ℝ}
    {A : Coefficient d K} {U : Set (Vec d)}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsParabolicSolution A (Set.Ioo a b) U u G) :
    IsParabolicSolution A (Set.Ioc a b) U u G := by
  have htime : (volume : Measure ℝ).restrict (Set.Ioo a b) =
      volume.restrict (Set.Ioc a b) := restrict_Ioo_eq_restrict_Ioc
  have hprod : (volume : Measure (ℝ × Vec d)).restrict (Set.Ioo a b ×ˢ U) =
      volume.restrict (Set.Ioc a b ×ˢ U) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict,
      ← Measure.prod_restrict, htime]
  simpa only [IsParabolicSolution, ← htime, ← hprod, interior_Ioc, interior_Ioo] using hsol

end EinsteinRelation.Correctors
