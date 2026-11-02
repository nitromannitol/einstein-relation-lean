import EinsteinRelation.Clock.AbelLimit
import EinsteinFull.Calculus.C5ComplexLaplacePrimitive
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
open MeasureTheory Filter
open scoped Topology
namespace EinsteinFull.Blueprint
/- SUPERVISOR EXACT CONTRACT (not a declaration/proof):
theorem complex_abel_limit_of_cesaro
    (f : ℝ → ℂ) (hf : Continuous f) (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ K) (L : ℂ)
    (hcesaro : Tendsto (fun T : ℝ => (T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T, f t)
      atTop (𝓝 L)) :
    Tendsto (fun s : ℝ => (s : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
      (Real.exp (-s * t) : ℂ) * f t) (𝓝[>] (0 : ℝ)) (𝓝 L)
-/
/-- A bounded continuous complex function inherits its Cesaro limit as an Abel limit. -/
theorem complex_abel_limit_of_cesaro
    (f : ℝ → ℂ) (hf : Continuous f) (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ K) (L : ℂ)
    (hcesaro : Tendsto (fun T : ℝ => (T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T, f t)
      atTop (𝓝 L)) :
    Tendsto (fun s : ℝ => (s : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
      (Real.exp (-s * t) : ℂ) * f t) (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  let F : ℝ → ℂ := fun t => ∫ u in (0 : ℝ)..t, f u
  have hFc : Continuous F :=
    (intervalIntegral.differentiable_integral_of_continuous hf).continuous
  have hFb (t : ℝ) (ht : 0 ≤ t) : ‖F t‖ ≤ K * t := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 0) (b := t) (C := K) (f := f) (fun u hu =>
        hbound u (by rw [Set.uIoc_of_le ht] at hu; exact hu.1.le))
    simpa only [sub_zero, abs_of_nonneg ht] using hb
  have hpart (p : ℂ →L[ℝ] ℝ) (hp : ∀ z, ‖p z‖ ≤ ‖z‖) :
      Tendsto (fun s : ℝ => s ^ 2 * ∫ t in Set.Ioi (0 : ℝ),
        Real.exp (-(s * t)) * p (F t)) (𝓝[>] (0 : ℝ)) (𝓝 (p L)) := by
    apply EinsteinRelation.Clock.abel_tendsto_of_bounded_rate (fun t => p (F t))
      (p.continuous.comp hFc).measurable K (p L)
    · intro t ht
      exact (hp (F t)).trans (hFb t ht)
    · have hh := p.continuous.continuousAt.tendsto.comp hcesaro
      convert hh using 1
      ext t
      change p (F t) / t = p ((t : ℂ)⁻¹ * F t)
      rw [← Complex.ofReal_inv, ← Complex.real_smul, map_smul]
      simp only [smul_eq_mul, div_eq_mul_inv, mul_comm]
  have hInt (s : ℝ) (hs : 0 < s) :
      IntegrableOn (fun t => (Real.exp (-s * t) : ℂ) * F t) (Set.Ioi 0) := by
    have ht : IntegrableOn (fun t : ℝ => t * Real.exp (-s * t)) (Set.Ioi 0) := by
      simpa only [Real.rpow_one] using
        (integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1)
          (by norm_num) zero_lt_one hs)
    apply (ht.const_mul K).mono'
      ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp
        (continuous_const.mul continuous_id))).mul hFc).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change ‖(Real.exp (-s * t) : ℂ) * F t‖ ≤ K * (t * Real.exp (-s * t))
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (-s * t) * ‖F t‖ ≤ Real.exp (-s * t) * (K * t) :=
        mul_le_mul_of_nonneg_left (hFb t ht.le) (Real.exp_pos _).le
      _ = K * (t * Real.exp (-s * t)) := by ring
  have hproject (p : ℂ →L[ℝ] ℝ) (s : ℝ) (hs : 0 < s) :
      p ((s : ℂ) ^ 2 * ∫ t in Set.Ioi (0 : ℝ),
        (Real.exp (-s * t) : ℂ) * F t) =
      s ^ 2 * ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(s * t)) * p (F t) := by
    rw [← Complex.ofReal_pow, ← Complex.real_smul, map_smul,
      ← p.integral_comp_comm (hInt s hs)]
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    dsimp only
    rw [← Complex.real_smul, map_smul]
    simp only [smul_eq_mul, neg_mul]
  have hre := hpart Complex.reCLM (fun z => Complex.abs_re_le_norm z)
  have him := hpart Complex.imCLM (fun z => Complex.abs_im_le_norm z)
  have hc : Tendsto (fun s : ℝ => (s : ℂ) ^ 2 * ∫ t in Set.Ioi (0 : ℝ),
      (Real.exp (-s * t) : ℂ) * F t) (𝓝[>] (0 : ℝ)) (𝓝 L) := by
    have hr : Tendsto (fun s : ℝ => (((s : ℂ) ^ 2 * ∫ t in Set.Ioi (0 : ℝ),
        (Real.exp (-s * t) : ℂ) * F t)).re) (𝓝[>] (0 : ℝ)) (𝓝 L.re) := by
      apply hre.congr'
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact (hproject Complex.reCLM s hs).symm
    have hi : Tendsto (fun s : ℝ => (((s : ℂ) ^ 2 * ∫ t in Set.Ioi (0 : ℝ),
        (Real.exp (-s * t) : ℂ) * F t)).im) (𝓝[>] (0 : ℝ)) (𝓝 L.im) := by
      apply him.congr'
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact (hproject Complex.imCLM s hs).symm
    simpa only [Complex.re_add_im] using hr.ofReal.add (hi.ofReal.mul_const Complex.I)
  apply hc.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (complex_laplace_primitive_identity f hf K hK hbound s hs).symm
end EinsteinFull.Blueprint
