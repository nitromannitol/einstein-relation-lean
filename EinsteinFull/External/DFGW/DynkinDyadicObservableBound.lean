import EinsteinFull.External.DFGW.DynkinDyadicSecondMoment
import EinsteinFull.External.DFGW.TimeIntegralSupremum

/-! # Dyadic observable bounds from Dynkin martingales

The supremum of a generator-domain observable on dyadic times is controlled by its initial
value, its Dynkin martingale, and the absolute integrated generator.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation
open scoped NNReal ENNReal

namespace EinsteinFull.External.DFGW

variable {S : Type} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- Every dyadic point in the grid of `[0,t]` lies in that interval. -/
theorem dyadicGridTime_le (t : ℝ≥0) (r k : ℕ) (hk : k ≤ 2 ^ r) :
    dyadicGridTime t r k ≤ t := by
  calc
    dyadicGridTime t r k ≤ dyadicGridTime t r (2 ^ r) :=
      nsmul_le_nsmul_left (show 0 ≤ t / ((2 ^ r : ℕ) : ℝ≥0) from bot_le) hk
    _ = t := dyadicGridTime_last t r

/-- On almost every path, all dyadic observable values are dominated by a Dynkin increment,
the initial value, and the absolute integrated generator. -/
theorem ae_abs_observable_dyadic_le
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (f : (transitionSemigroup hP).generatorDomain) (t : ℝ≥0) :
    ∀ᵐ η ∂P, ∀ r k : ℕ, k ≤ 2 ^ r →
      |(f : Lp ℝ 2 μ) (η (dyadicGridTime t r k))| ≤
        |dynkinProcess hP f (dyadicGridTime t r k) η - dynkinProcess hP f 0 η| +
        |(f : Lp ℝ 2 μ) (η 0)| +
        ∫ u in (0 : ℝ)..t, |(transitionSemigroup hP).generator f (η u)| := by
  let : IsProbabilityMeasure μ := hP.invariant_probability
  let g := (transitionSemigroup hP).generator f
  have hg : Integrable g μ := (Lp.memLp g).integrable one_le_two
  filter_upwards [ae_abs_time_integral_le_integral_abs hP g hg t] with η hη r k hk
  let s := dyadicGridTime t r k
  have hs : s ≤ t := dyadicGridTime_le t r k hk
  have hint := hη s hs
  have hid : (f : Lp ℝ 2 μ) (η s) =
      (dynkinProcess hP f s η - dynkinProcess hP f 0 η) +
        (f : Lp ℝ 2 μ) (η 0) + ∫ u in (0 : ℝ)..s, g (η u) := by
    simp only [dynkinProcess, NNReal.coe_zero, intervalIntegral.integral_same, sub_zero]
    ring
  change |(f : Lp ℝ 2 μ) (η s)| ≤
    |dynkinProcess hP f s η - dynkinProcess hP f 0 η| +
      |(f : Lp ℝ 2 μ) (η 0)| + ∫ u in (0 : ℝ)..t, |g (η u)|
  rw [hid]
  have htri := abs_add_le
    ((dynkinProcess hP f s η - dynkinProcess hP f 0 η) + (f : Lp ℝ 2 μ) (η 0))
    (∫ u in (0 : ℝ)..s, g (η u))
  have htri' := abs_add_le (dynkinProcess hP f s η - dynkinProcess hP f 0 η)
    ((f : Lp ℝ 2 μ) (η 0))
  linarith

end EinsteinFull.External.DFGW
