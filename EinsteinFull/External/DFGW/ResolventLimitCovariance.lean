import EinsteinFull.External.DFGW.ResolventLimitStationary

/-! # Covariance of the limiting resolvent martingale

The limiting martingale has stationary increments with variance proportional to elapsed time,
and its covariance is proportional to the earlier time.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The squared `L²` norm of a limiting martingale increment is linear in its duration. -/
theorem norm_resolvent_limit_increment_sq (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (f : Lp ℝ 2 μ)
    (hint : IntegrableOn (fun t : ℝ => inner ℝ f (transitionOperator hP t.toNNReal f))
      (Set.Ioi 0)) (Z : ℝ≥0 → Lp ℝ 2 P)
    (hZ : ∀ t, Tendsto (fun n : ℕ => dynkinIncrementLp hP
      (transitionResolventDomain hP (reciprocalShift n) f) t) atTop (𝓝 (Z t)))
    (s t : ℝ≥0) :
    ‖Z (s + t) - Z s‖ ^ 2 = (t : ℝ) * (2 * ∫ u in Set.Ioi (0 : ℝ),
      inner ℝ f (transitionOperator hP u.toNNReal f)) := by
  have hs := resolvent_limit_stationary_increments hP f Z hZ s t
  rw [hs, Lp.norm_compMeasurePreserving]
  exact norm_resolvent_martingale_limit_sq hP hcoord f hint Z hZ t

/-- The covariance of the limiting martingale at two ordered times is its earlier variance. -/
theorem inner_resolvent_martingale_limit (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (f : Lp ℝ 2 μ)
    (hint : IntegrableOn (fun t : ℝ => inner ℝ f (transitionOperator hP t.toNNReal f))
      (Set.Ioi 0)) (Z : ℝ≥0 → Lp ℝ 2 P)
    (hZ : ∀ t, Tendsto (fun n : ℕ => dynkinIncrementLp hP
      (transitionResolventDomain hP (reciprocalShift n) f) t) atTop (𝓝 (Z t)))
    {s t : ℝ≥0} (hst : s ≤ t) :
    inner ℝ (Z s) (Z t) = (s : ℝ) * (2 * ∫ u in Set.Ioi (0 : ℝ),
      inner ℝ f (transitionOperator hP u.toNNReal f)) := by
  have hsqS := norm_resolvent_martingale_limit_sq hP hcoord f hint Z hZ s
  have hsqT := norm_resolvent_martingale_limit_sq hP hcoord f hint Z hZ t
  have hinc := norm_resolvent_limit_increment_sq hP hcoord f hint Z hZ s (t - s)
  have hadd : s + (t - s) = t := add_tsub_cancel_of_le hst
  rw [hadd, norm_sub_sq_real] at hinc
  simp only [NNReal.coe_sub hst] at hinc
  have hsym : inner ℝ (Z t) (Z s) = inner ℝ (Z s) (Z t) := real_inner_comm _ _
  rw [hsym] at hinc
  nlinarith

end EinsteinFull.External.DFGW
