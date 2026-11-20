import EinsteinFull.External.DFGW.DoobDyadicGrid
import EinsteinFull.External.DFGW.DynkinCentered

/-! # Dyadic maxima of Dynkin martingales

A generator-domain Dynkin martingale has a square-integrable supremum over dyadic times
on each bounded interval.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation
open scoped NNReal ENNReal

namespace EinsteinFull.External.DFGW

variable {S : Type} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The supremum of a centered Dynkin martingale on dyadic times has finite second moment. -/
theorem lintegral_sup_dyadic_dynkin_increment_lt_top
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (f : (transitionSemigroup hP).generatorDomain) (t : ℝ≥0) :
    (∫⁻ η, ⨆ r : ℕ, (⨆ k ≤ 2 ^ r, ENNReal.ofReal
      |dynkinProcess hP f (dyadicGridTime t r k) η - dynkinProcess hP f 0 η|) ^ 2 ∂P) < ⊤ := by
  let : IsProbabilityMeasure P := hP.probability
  let M : ℝ≥0 → C(ℝ, S) → ℝ := fun t η => dynkinProcess hP f t η - dynkinProcess hP f 0 η
  have hM : Martingale M Draft.dfgwPast P := martingale_dynkin_increment hP hcoord f
  have hzero : ∀ η, M 0 η = 0 := fun η => sub_self _
  have hM2 : MemLp (M t) 2 P := (dynkinProcess_memLp hP f t).sub (dynkinProcess_memLp hP f 0)
  exact lintegral_sup_dyadic_martingale_lt_top M hM hzero t hM2

end EinsteinFull.External.DFGW
