import EinsteinRelation.Calculus.HorizontalMollification
import EinsteinRelation.Correctors.KernelLpContraction
import EinsteinRelation.Environment.LocalIntegralMeasurability
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.WithDensity

/-! # Compact-kernel convolution of stationary fields

Source: `paper/main.tex:1018–1031`, Step 2 of Proposition 6.1. Signed
integrable kernels act on the actual translation orbits with operator norm at
most their `L¹` mass. The localization theorem applies to the same integral.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace EinsteinRelation.Correctors

variable {d : ℕ}

/-- Integrable stationary fields and integrable spatial kernels have an
integrable joint orbit integrand (`paper/main.tex:1018–1031`). -/
theorem integrable_kernel_translate {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) {K : Vec d → ℝ} (hK : Measurable K)
    (hKi : Integrable K volume) {f : FieldPair d → ℝ} (hf : Measurable f)
    (hfi : Integrable f Q) :
    Integrable (fun q : FieldPair d × Vec d => K q.2 * f (translate q.2 q.1))
      (Q.prod volume) := by
  have ht : Measurable (fun q : FieldPair d × Vec d => translate q.2 q.1) :=
    Probability.continuous_translate.measurable.comp measurable_swap
  have hmeas : Measurable (fun q : FieldPair d × Vec d =>
      K q.2 * f (translate q.2 q.1)) := (hK.comp measurable_snd).mul (hf.comp ht)
  rw [integrable_prod_iff' hmeas.aestronglyMeasurable]
  refine ⟨ae_of_all _ fun z => ?_, ?_⟩
  · have hshift : Integrable f (Measure.map (translate z) Q) := by
      rw [hQ z]
      exact hfi
    exact (hshift.comp_measurable (Probability.measurable_translate z)).const_mul (K z)
  · have hnorm (z : Vec d) :
        (∫ ω, ‖K z * f (translate z ω)‖ ∂Q) = ‖K z‖ * ∫ ω, ‖f ω‖ ∂Q := by
      simp_rw [norm_mul]
      rw [integral_const_mul, Probability.integral_translate Q hQ z _ hf.norm]
    simpa only [hnorm] using hKi.norm.mul_const (∫ ω, ‖f ω‖ ∂Q)

/-- Almost every actual orbit gives an integrable convolution integrand
(`paper/main.tex:1018–1031`). -/
theorem ae_integrable_kernel_translate {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) {K : Vec d → ℝ} (hK : Measurable K)
    (hKi : Integrable K volume) {f : FieldPair d → ℝ} (hf : Measurable f)
    (hfi : Integrable f Q) :
    ∀ᵐ ω ∂Q, Integrable (fun z => K z * f (translate z ω)) volume :=
  (integrable_kernel_translate hQ hK hKi hf hfi).prod_right_ae

/-- Averaging stationary translates against a probability measure, with a
multiplier of absolute value at most one, contracts every finite `L^p` norm
(`paper/main.tex:1018–1031`). -/
theorem eLpNorm_integral_stationary_le {Q : Measure (FieldPair d)} [SFinite Q]
    (hQ : IsStationary Q) (ν : Measure (Vec d)) [IsProbabilityMeasure ν]
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    {f : FieldPair d → ℝ} (hf : Measurable f)
    {a : Vec d → ℝ} (ha : Measurable a) (hab : ∀ z, |a z| ≤ 1) :
    eLpNorm (fun ω => ∫ z, a z * f (translate z ω) ∂ν) p Q ≤ eLpNorm f p Q := by
  have ht : Measurable (fun q : FieldPair d × Vec d => translate q.2 q.1) :=
    Probability.continuous_translate.measurable.comp measurable_swap
  have hF : StronglyMeasurable (fun q : FieldPair d × Vec d =>
      a q.2 * f (translate q.2 q.1)) :=
    ((ha.comp measurable_snd).mul (hf.comp ht)).stronglyMeasurable
  have hJ := eLpNorm_kernel_integral_le (μ := Q) (Kernel.const (FieldPair d) ν) hp hp_top hF
  simp only [Kernel.const_apply, Measure.compProd_const] at hJ
  apply hJ.trans
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top hF.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top hf.aestronglyMeasurable]
  apply ENNReal.rpow_le_rpow _ (one_div_nonneg.mpr hpr.le)
  rw [lintegral_prod_symm _ (hF.enorm.pow_const p.toReal).aemeasurable]
  calc
    (∫⁻ z, ∫⁻ ω, ‖a z * f (translate z ω)‖ₑ ^ p.toReal ∂Q ∂ν) ≤
        ∫⁻ z, ∫⁻ ω, ‖f (translate z ω)‖ₑ ^ p.toReal ∂Q ∂ν := by
      apply lintegral_mono
      intro z
      apply lintegral_mono
      intro ω
      apply ENNReal.rpow_le_rpow _ hpr.le
      rw [← ofReal_norm, ← ofReal_norm]
      apply ENNReal.ofReal_le_ofReal
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (hab z)
    _ = ∫⁻ ω, ‖f ω‖ₑ ^ p.toReal ∂Q := by
      have hshift : ∀ z : Vec d,
          (∫⁻ ω, ‖f (translate z ω)‖ₑ ^ p.toReal ∂Q) = ∫⁻ ω, ‖f ω‖ₑ ^ p.toReal ∂Q := by
        intro z
        rw [← lintegral_map (hf.enorm.pow_const p.toReal) (Probability.measurable_translate z),
          hQ z]
      simp only [hshift, lintegral_const, measure_univ, mul_one]

/-- Signed orbit convolution has the usual `L¹ × L^p → L^p` bound for
stationary laws (`paper/main.tex:1018–1031`). -/
theorem eLpNorm_horizontalMollify_le {Q : Measure (FieldPair d)} [SFinite Q]
    (hQ : IsStationary Q) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    {K : Vec d → ℝ} (hK : Measurable K) (hKi : Integrable K volume)
    {f : FieldPair d → ℝ} (hf : Measurable f) :
    eLpNorm (horizontalMollify K f) p Q ≤
      ENNReal.ofReal (∫ z, |K z|) * eLpNorm f p Q := by
  let A : ℝ := ∫ z, |K z|
  have hA : 0 ≤ A := integral_nonneg fun z => abs_nonneg _
  by_cases hA0 : A = 0
  · have hzero : K =ᵐ[volume] 0 := by
      have habszero : (fun z => |K z|) =ᵐ[volume] 0 :=
        (integral_eq_zero_iff_of_nonneg (fun z => abs_nonneg _) hKi.abs).mp hA0
      filter_upwards [habszero] with z hz
      exact abs_eq_zero.mp hz
    have hfun : horizontalMollify K f = 0 := by
      funext ω
      apply integral_eq_zero_of_ae
      filter_upwards [hzero] with z hz
      simp only [Pi.zero_apply] at hz
      simp only [hz, zero_mul, Pi.zero_apply]
    rw [hfun, eLpNorm_zero]
    exact zero_le
  have hKabs : Measurable (fun z => |K z|) := continuous_abs.measurable.comp hK
  let w : Vec d → ℝ≥0∞ := fun z => ENNReal.ofReal (|K z| / A)
  have hw : Measurable w := (hKabs.div_const A).ennreal_ofReal
  let ν : Measure (Vec d) := volume.withDensity w
  have hν : IsProbabilityMeasure ν := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [← ofReal_integral_eq_lintegral_ofReal (hKi.abs.div_const A)
      (ae_of_all _ fun z => div_nonneg (abs_nonneg _) hA), integral_div]
    change ENNReal.ofReal (A / A) = 1
    rw [div_self hA0, ENNReal.ofReal_one]
  letI := hν
  let a : Vec d → ℝ := fun z => K z / |K z|
  have ha : Measurable a := hK.div hKabs
  have hab : ∀ z, |a z| ≤ 1 := by
    intro z
    dsimp [a]
    rw [abs_div, abs_abs]
    by_cases hz : K z = 0
    · simp only [hz, abs_zero, div_zero, zero_le_one]
    · exact le_of_eq (div_self (abs_ne_zero.mpr hz))
  have hrep : horizontalMollify K f =
      A • (fun ω => ∫ z, a z * f (translate z ω) ∂ν) := by
    funext ω
    change (∫ z, K z * f (translate z ω)) = A * ∫ z, a z * f (translate z ω) ∂ν
    rw [integral_withDensity_eq_integral_toReal_smul hw
      (ae_of_all _ fun z => ENNReal.ofReal_lt_top)]
    rw [← integral_const_mul]
    apply integral_congr_ae
    apply ae_of_all
    intro z
    dsimp only [w, a]
    rw [ENNReal.toReal_ofReal (div_nonneg (abs_nonneg _) hA), smul_eq_mul]
    by_cases hz : K z = 0
    · simp only [hz, abs_zero, zero_mul, zero_div, mul_zero]
    · field_simp
  rw [hrep, eLpNorm_const_smul, Real.enorm_eq_ofReal hA]
  exact mul_le_mul_right (eLpNorm_integral_stationary_le hQ ν hp hp_top hf ha hab) _

/-- Convolution preserves finite moments of unbounded stationary fields
(`paper/main.tex:1018–1031`). -/
theorem memLp_horizontalMollify {Q : Measure (FieldPair d)} [SFinite Q]
    (hQ : IsStationary Q) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    {K : Vec d → ℝ} (hK : Measurable K) (hKi : Integrable K volume)
    {f : FieldPair d → ℝ} (hf : Measurable f) (hfp : MemLp f p Q) :
    MemLp (horizontalMollify K f) p Q := by
  rw [memLp_iff]
  refine (eLpNorm_horizontalMollify_le hQ hp hp_top hK hKi hf).trans_lt ?_
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (memLp_iff.mp hfp)

/-- A kernel supported in `S`, applied to a field observed on `U`, is local on
any window containing `S + U` (`paper/main.tex:1069–1074`). -/
theorem measurable_localSigma_horizontalMollify {S U W : Set (Vec d)}
    (hS : MeasurableSet S) (hSW : ∀ x ∈ S, ∀ y ∈ U, x + y ∈ W)
    {K : Vec d → ℝ} (hK : Measurable K) (hsupp : Function.support K ⊆ S)
    {f : FieldPair d → ℝ} (hf : Measurable[localSigma U] f) :
    Measurable[localSigma W] (horizontalMollify K f) := by
  have hrep : horizontalMollify K f = fun ω => ∫ x in S, K x * f (translate x ω) := by
    funext ω
    rw [horizontalMollify, ← integral_indicator hS]
    apply integral_congr_ae
    apply ae_of_all
    intro x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      have hzero : K x = 0 := by
        by_contra hn
        exact hx (hsupp hn)
      change K x * f (translate x ω) = 0
      rw [hzero, zero_mul]
  rw [hrep]
  exact measurable_localSigma_setIntegral_translate hS hSW K hK f hf

end EinsteinRelation.Correctors
