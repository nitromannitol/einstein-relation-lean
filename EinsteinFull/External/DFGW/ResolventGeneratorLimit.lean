import EinsteinFull.External.DFGW.ResolventEnergyCauchy

/-! # Generator limit for resolvent approximations

The generators of resolvent approximations converge to the negative of the original observable.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The normalized resolvent tends to zero in `L²`. -/
theorem tendsto_reciprocalShift_smul_resolvent
    (hP : Draft.IsDFGWTrajectoryProcess P μ T) (f : Lp ℝ 2 μ)
    (hint : IntegrableOn (fun t : ℝ => inner ℝ f (transitionOperator hP t.toNNReal f))
      (Set.Ioi 0)) :
    Tendsto (fun n : ℕ => (reciprocalShift n : ℝ) •
      transitionResolvent hP (reciprocalShift n) f) atTop (𝓝 0) := by
  have hlam : Tendsto (fun n => (reciprocalShift n : ℝ)) atTop (𝓝 0) := by
    simpa only [reciprocalShift] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have h := hlam.mul (tendsto_reciprocalShift_mul_resolvent_norm_sq hP f hint)
  have hsq : Tendsto (fun n : ℕ => ‖(reciprocalShift n : ℝ) •
      transitionResolvent hP (reciprocalShift n) f‖ ^ 2) atTop (𝓝 0) := by
    convert h using 1
    · funext n
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (reciprocalShift n).2]
      ring
    · simp
  have hroot := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simp only [Real.sqrt_zero] at hroot
  rw [tendsto_zero_iff_norm_tendsto_zero]
  convert hroot using 1
  funext n
  simp only [Function.comp_apply]
  rw [Real.sqrt_sq (norm_nonneg _)]

/-- The generator of a resolvent approximation tends to the negative observable in `L²`. -/
theorem tendsto_generator_reciprocalShift_resolvent
    (hP : Draft.IsDFGWTrajectoryProcess P μ T) (f : Lp ℝ 2 μ)
    (hint : IntegrableOn (fun t : ℝ => inner ℝ f (transitionOperator hP t.toNNReal f))
      (Set.Ioi 0)) :
    Tendsto (fun n : ℕ => (transitionSemigroup hP).generator
      (transitionResolventDomain hP (reciprocalShift n) f)) atTop (𝓝 (-f)) := by
  have h := (tendsto_reciprocalShift_smul_resolvent hP f hint).sub (tendsto_const_nhds (x := f))
  simpa only [zero_sub] using h.congr' (Filter.Eventually.of_forall fun n => by
    dsimp only [transitionResolventDomain, transitionResolvent]
    rw [(transitionSemigroup hP).generator_resolvent])

end EinsteinFull.External.DFGW
