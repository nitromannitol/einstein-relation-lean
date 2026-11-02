import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
open MeasureTheory Filter
open scoped Topology
namespace EinsteinFull.Blueprint
/- SUPERVISOR EXACT CONTRACT (not a declaration/proof):
theorem complex_laplace_primitive_identity
    (f : ℝ → ℂ) (hf : Continuous f) (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ K) (s : ℝ) (hs : 0 < s) :
    (s : ℂ) * (∫ t in Set.Ioi (0 : ℝ), (Real.exp (-s * t) : ℂ) * f t) =
      (s : ℂ) ^ 2 * (∫ t in Set.Ioi (0 : ℝ),
        (Real.exp (-s * t) : ℂ) * ∫ u in (0 : ℝ)..t, f u)
-/

/-- Integration by parts relates a bounded function's Laplace integral to that of its primitive. -/
theorem complex_laplace_primitive_identity
    (f : ℝ → ℂ) (hf : Continuous f) (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ K) (s : ℝ) (hs : 0 < s) :
    (s : ℂ) * (∫ t in Set.Ioi (0 : ℝ), (Real.exp (-s * t) : ℂ) * f t) =
      (s : ℂ) ^ 2 * (∫ t in Set.Ioi (0 : ℝ),
        (Real.exp (-s * t) : ℂ) * ∫ u in (0 : ℝ)..t, f u) := by
  let F : ℝ → ℂ := fun t => ∫ u in (0 : ℝ)..t, f u
  let e : ℝ → ℂ := fun t => (Real.exp (-s * t) : ℂ)
  have hFderiv (t : ℝ) : HasDerivAt F (f t) t :=
    intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable _ _)
      hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  have hFc : Continuous F :=
    (intervalIntegral.differentiable_integral_of_continuous hf).continuous
  have hec : Continuous e := by dsimp [e]; fun_prop
  have hFbound (t : ℝ) (ht : 0 ≤ t) : ‖F t‖ ≤ K * t := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 0) (b := t) (C := |K|) (f := f) (fun u hu =>
        (hbound u (by rw [Set.uIoc_of_le ht] at hu; exact hu.1.le)).trans (le_abs_self K))
    simpa only [sub_zero, abs_of_nonneg ht, abs_of_nonneg hK] using hb
  have henorm (t : ℝ) : ‖e t‖ = Real.exp (-s * t) := by
    simp only [e, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hexp : IntegrableOn (fun t : ℝ => Real.exp (-s * t)) (Set.Ioi 0) :=
    integrableOn_exp_mul_Ioi (neg_neg_of_pos hs) 0
  have htexp : IntegrableOn (fun t : ℝ => t * Real.exp (-s * t)) (Set.Ioi 0) := by
    simpa only [Real.rpow_one] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1)
        (by norm_num) zero_lt_one hs)
  have hef : IntegrableOn (fun t => e t * f t) (Set.Ioi 0) := by
    apply (hexp.const_mul K).mono' (hec.mul hf).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Pi.mul_apply, norm_mul, henorm]
    calc
      Real.exp (-s * t) * ‖f t‖ ≤ Real.exp (-s * t) * K :=
        mul_le_mul_of_nonneg_left (hbound t ht.le) (Real.exp_pos _).le
      _ = K * Real.exp (-s * t) := mul_comm _ _
  have heF : IntegrableOn (fun t => e t * F t) (Set.Ioi 0) := by
    apply (htexp.const_mul K).mono' (hec.mul hFc).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Pi.mul_apply, norm_mul, henorm]
    calc
      Real.exp (-s * t) * ‖F t‖ ≤ Real.exp (-s * t) * (K * t) :=
        mul_le_mul_of_nonneg_left (hFbound t ht.le) (Real.exp_pos _).le
      _ = K * (t * Real.exp (-s * t)) := by ring
  have hederiv (t : ℝ) : HasDerivAt e (-(s : ℂ) * e t) t := by
    have hd := (((hasDerivAt_id t).const_mul (-s)).exp).ofReal_comp
    simpa only [e, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_one, mul_one, id_eq, mul_comm] using hd
  have hzero : Tendsto (e * F) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (0 : ℂ)) := by
    have hz : (e * F) 0 = 0 := by simp [F, Pi.mul_apply]
    rw [← hz]
    exact (hec.mul hFc).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hinfty : Tendsto (e * F) atTop (𝓝 (0 : ℂ)) := by
    apply squeeze_zero_norm' (a := fun t => K * (t * Real.exp (-s * t)))
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      simp only [Pi.mul_apply, norm_mul, henorm]
      calc
        Real.exp (-s * t) * ‖F t‖ ≤ Real.exp (-s * t) * (K * t) :=
          mul_le_mul_of_nonneg_left (hFbound t ht) (Real.exp_pos _).le
        _ = K * (t * Real.exp (-s * t)) := by ring
    · simpa only [Real.rpow_one, mul_zero] using
        (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 s hs).const_mul K
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (u := e) (u' := fun t => -(s : ℂ) * e t)
    (v := F) (v' := f) (fun t _ => hederiv t) (fun t _ => hFderiv t)
    hef (by simpa only [IntegrableOn, Pi.mul_def, mul_assoc] using heF.const_mul (-(s : ℂ)))
    hzero hinfty
  have hi : (∫ t in Set.Ioi (0 : ℝ), e t * f t) =
      (s : ℂ) * ∫ t in Set.Ioi (0 : ℝ), e t * F t := by
    simp only [mul_assoc, integral_const_mul] at hibp
    simpa only [sub_self, zero_sub, neg_mul, neg_neg] using hibp
  change (s : ℂ) * (∫ t in Set.Ioi (0 : ℝ), e t * f t) =
    (s : ℂ) ^ 2 * ∫ t in Set.Ioi (0 : ℝ), e t * F t
  rw [hi]
  ring

end EinsteinFull.Blueprint
