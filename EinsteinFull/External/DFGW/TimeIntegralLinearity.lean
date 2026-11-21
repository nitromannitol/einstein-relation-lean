import EinsteinFull.External.DFGW.TimeIntegralLp
import EinsteinFull.External.DFGW.TimeIntegralCongruence

/-! # Linearity of time integration in `L²`

Time integration along a stationary trajectory respects the vector space structure of state
`L²` observables.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- Time integration respects subtraction of square-integrable state observables. -/
theorem timeIntegralLp_sub (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (f g : Lp ℝ 2 μ) (t : ℝ≥0) :
    timeIntegralLp hP (f - g) t = timeIntegralLp hP f t - timeIntegralLp hP g t := by
  let : IsProbabilityMeasure P := hP.probability
  let : IsProbabilityMeasure μ := hP.invariant_probability
  have hrepr (h : Lp ℝ 2 μ) : timeIntegralLp hP h t =ᵐ[P]
      fun η => ∫ u in (0 : ℝ)..t, h (η u) :=
    MemLp.coeFn_toLp ((time_integral_memLp_and_sq_le hP h (Lp.memLp h) t.coe_nonneg).1)
  have hcongr := ae_time_integral_congr hP (Lp.coeFn_sub f g) t.coe_nonneg
  have hf := (integrable_joint_observable hP f ((Lp.memLp f).integrable one_le_two) 0 t).prod_left_ae
  have hg := (integrable_joint_observable hP g ((Lp.memLp g).integrable one_le_two) 0 t).prod_left_ae
  apply Lp.ext
  filter_upwards [hrepr (f - g), hrepr f, hrepr g, Lp.coeFn_sub (timeIntegralLp hP f t)
    (timeIntegralLp hP g t), hcongr, hf, hg] with η hfg hff hgg hsub hc hfη hgη
  have hiF := (intervalIntegrable_iff_integrableOn_Ioc_of_le t.coe_nonneg).2 hfη
  have hiG := (intervalIntegrable_iff_integrableOn_Ioc_of_le t.coe_nonneg).2 hgη
  simp only [Pi.sub_apply] at hsub hc
  rw [hfg, hsub, hff, hgg, hc, intervalIntegral.integral_sub hiF hiG]

/-- Time integration respects scalar multiplication of square-integrable state observables. -/
theorem timeIntegralLp_smul (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (c : ℝ) (f : Lp ℝ 2 μ) (t : ℝ≥0) :
    timeIntegralLp hP (c • f) t = c • timeIntegralLp hP f t := by
  have hrepr (h : Lp ℝ 2 μ) : timeIntegralLp hP h t =ᵐ[P]
      fun η => ∫ u in (0 : ℝ)..t, h (η u) :=
    MemLp.coeFn_toLp ((time_integral_memLp_and_sq_le hP h (Lp.memLp h) t.coe_nonneg).1)
  have hcongr := ae_time_integral_congr hP (Lp.coeFn_smul c f) t.coe_nonneg
  apply Lp.ext
  filter_upwards [hrepr (c • f), hrepr f, Lp.coeFn_smul c (timeIntegralLp hP f t), hcongr] with η hcf hf hs hc
  simp only [Pi.smul_apply, smul_eq_mul] at hs hc
  rw [hcf, hs, hf, hc, intervalIntegral.integral_const_mul]

end EinsteinFull.External.DFGW
