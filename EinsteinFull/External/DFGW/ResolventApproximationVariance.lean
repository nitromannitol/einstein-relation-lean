import EinsteinFull.External.DFGW.ResolventDecomposition

/-! # Variance of the resolvent martingale approximation

At every fixed approximation index, the squared `L²` distance to the limiting martingale is
proportional to time.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The squared distance between a resolvent martingale and its limit scales linearly in time. -/
theorem norm_resolvent_martingale_sub_limit_sq (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (f : Lp ℝ 2 μ) (Z : ℝ≥0 → Lp ℝ 2 P)
    (hZ : ∀ t, Tendsto (fun n : ℕ => dynkinIncrementLp hP
      (transitionResolventDomain hP (reciprocalShift n) f) t) atTop (𝓝 (Z t)))
    (n : ℕ) (t : ℝ≥0) :
    ‖dynkinIncrementLp hP (transitionResolventDomain hP (reciprocalShift n) f) t - Z t‖ ^ 2 =
      (t : ℝ) * ‖dynkinIncrementLp hP (transitionResolventDomain hP (reciprocalShift n) f) 1 - Z 1‖ ^ 2 := by
  let D : ℕ → ℝ≥0 → Lp ℝ 2 P := fun m u => dynkinIncrementLp hP
    (transitionResolventDomain hP (reciprocalShift m) f) u
  have heq (m : ℕ) : ‖D n t - D m t‖ ^ 2 = (t : ℝ) * ‖D n 1 - D m 1‖ ^ 2 := by
    rw [norm_dynkinIncrementLp_sub_sq hP hcoord _ _ t,
      norm_dynkinIncrementLp_sub_sq hP hcoord _ _ 1]
    simp only [NNReal.coe_one, one_mul]
  have hleft : Tendsto (fun m : ℕ => ‖D n t - D m t‖ ^ 2) atTop
      (𝓝 (‖D n t - Z t‖ ^ 2)) := ((tendsto_const_nhds.sub (hZ t)).norm).pow 2
  have hright : Tendsto (fun m : ℕ => (t : ℝ) * ‖D n 1 - D m 1‖ ^ 2) atTop
      (𝓝 ((t : ℝ) * ‖D n 1 - Z 1‖ ^ 2)) :=
    (((tendsto_const_nhds.sub (hZ 1)).norm).pow 2).const_mul (t : ℝ)
  have hfunc : (fun m : ℕ => ‖D n t - D m t‖ ^ 2) =
      (fun m : ℕ => (t : ℝ) * ‖D n 1 - D m 1‖ ^ 2) := funext heq
  rw [hfunc] at hleft
  exact tendsto_nhds_unique hleft hright

end EinsteinFull.External.DFGW
