import EinsteinFull.External.DFGW.ResolventLimitMartingale

/-! # Limit of resolvent energies

The generator energies of the resolvent approximations converge to the integrated
stationary autocorrelation.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The generator energy of resolvent approximations converges to the correlation integral. -/
theorem tendsto_resolvent_generator_energy (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (f : Lp ℝ 2 μ)
    (hint : IntegrableOn (fun t : ℝ => inner ℝ f (transitionOperator hP t.toNNReal f))
      (Set.Ioi 0)) :
    Tendsto (fun n : ℕ =>
      -inner ℝ (transitionResolventDomain hP (reciprocalShift n) f : Lp ℝ 2 μ)
        ((transitionSemigroup hP).generator (transitionResolventDomain hP (reciprocalShift n) f)))
      atTop (𝓝 (∫ t in Set.Ioi (0 : ℝ), inner ℝ f (transitionOperator hP t.toNNReal f))) := by
  have hpair := tendsto_reciprocalShift_pairing hP f hint
  have hsmall := tendsto_reciprocalShift_mul_resolvent_norm_sq hP f hint
  have h := hpair.sub hsmall
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards with n
  change _ = -inner ℝ (transitionResolvent hP (reciprocalShift n) f)
    ((transitionSemigroup hP).generator (transitionResolventDomain hP (reciprocalShift n) f))
  have hgen : (transitionSemigroup hP).generator (transitionResolventDomain hP (reciprocalShift n) f) =
      (reciprocalShift n : ℝ) • transitionResolvent hP (reciprocalShift n) f - f := by
    dsimp only [transitionResolventDomain, transitionResolvent]
    exact (transitionSemigroup hP).generator_resolvent (reciprocalShift n) f
  rw [hgen, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, real_inner_comm]
  ring

end EinsteinFull.External.DFGW
