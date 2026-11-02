import EinsteinFull.Work.W7.ClockFiniteRangeSupport
import EinsteinFull.Calculus.SchwartzNormSupport
import EinsteinFull.Calculus.SpatialPairingSupport
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.Calculus.MeanValue
import EinsteinFull.Frozen.StructuralData
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# The covariance integral of the actual finite-range clock

The law in this file is the literal reduced joint law. The scalar covariance
is constructed from that law, independently of the spatial tests and scales.
All spatial integrals use ordinary Lebesgue measure.
-/

open MeasureTheory Filter

noncomputable section

namespace EinsteinFull

open EinsteinRelation

variable {d : ℕ} {Λ₀ r₀ : ℝ}

/-- The displacement covariance of the actual centered clock. -/
noncomputable def clockCovarianceKernel (Q : EnvironmentLaw d Λ₀ r₀) (z : Vec d) : ℝ :=
  clockCovariance Q z 0

/-- Stationarity identifies the two-point kernel with a displacement kernel. -/
theorem clockCovariance_eq_kernel (Q : EnvironmentLaw d Λ₀ r₀) (x y : Vec d) :
    clockCovariance Q x y = clockCovarianceKernel Q (x - y) := by
  simpa only [clockCovarianceKernel, add_sub_cancel, add_zero] using!
    clockCovariance_translate Q (x - y) 0 y

/-- Measurability follows from the actual product clock evaluation. -/
theorem measurable_clockCovarianceKernel (Q : EnvironmentLaw d Λ₀ r₀) :
    Measurable (clockCovarianceKernel Q) :=
  (measurable_clockCovariance Q).comp (measurable_id.prodMk measurable_const)

/-- Symmetry uses bilinear multiplication of the real clock. -/
theorem clockCovarianceKernel_neg (Q : EnvironmentLaw d Λ₀ r₀) (z : Vec d) :
    clockCovarianceKernel Q (-z) = clockCovarianceKernel Q z := by
  calc
    _ = clockCovariance Q 0 z := by
      rw [clockCovariance_eq_kernel, zero_sub]
    _ = clockCovariance Q z 0 := by
      unfold clockCovariance
      exact integral_congr_ae (ae_of_all _ fun _ => mul_comm _ _)
    _ = _ := rfl

/-- Joint finite range gives literal Euclidean compact support. -/
theorem clockCovarianceKernel_eq_zero (Q : EnvironmentLaw d Λ₀ r₀) (z : Vec d)
    (hz : r₀ < euclideanNorm z) : clockCovarianceKernel Q z = 0 := by
  exact clockCovariance_eq_zero Q z 0 (by simpa only [sub_zero] using! hz)

private theorem integrable_clockMajorant :
    Integrable (clockCovarianceMajorant d Λ₀ r₀) :=
  (integrableOn_const (isCompact_Icc.measure_lt_top.ne)).integrable_indicator measurableSet_Icc

/-- Compact-support domination constructs integrability, without a mixing premise. -/
theorem integrable_clockCovarianceKernel (Q : EnvironmentLaw d Λ₀ r₀) :
    Integrable (clockCovarianceKernel Q) := by
  apply integrable_clockMajorant.mono' (measurable_clockCovarianceKernel Q).aestronglyMeasurable
  exact ae_of_all _ fun z => by
    simpa only [clockCovarianceKernel, sub_zero, Real.norm_eq_abs] using!
      abs_clockCovariance_le_majorant Q z 0

/-- The total absolute covariance has a common structural bound. -/
theorem integral_abs_clockCovarianceKernel_le (Q : EnvironmentLaw d Λ₀ r₀) :
    (∫ z, |clockCovarianceKernel Q z|) ≤ clockVarianceConstant d Λ₀ r₀ := by
  rw [← integral_clockCovarianceMajorant (d := d) (Λ₀ := Λ₀)
    (zero_le_one.trans Q.range_parameter)]
  exact integral_mono (integrable_clockCovarianceKernel Q).abs integrable_clockMajorant
    (fun z => by simpa only [clockCovarianceKernel, sub_zero] using!
      abs_clockCovariance_le_majorant Q z 0)

/-- The law-dependent scalar clock-clock covariance, chosen before all tests. -/
noncomputable def clockCovarianceLimit (Q : EnvironmentLaw d Λ₀ r₀) : ℝ :=
  ∫ z, clockCovarianceKernel Q z

/-- A structural bound for the actual covariance integral. -/
theorem abs_clockCovarianceLimit_le (Q : EnvironmentLaw d Λ₀ r₀) :
    |clockCovarianceLimit Q| ≤ clockVarianceConstant d Λ₀ r₀ :=
  abs_integral_le_integral_abs.trans (integral_abs_clockCovarianceKernel_le Q)

private theorem clockKernel_moment_bound (Q : EnvironmentLaw d Λ₀ r₀) (z : Vec d) :
    ‖euclideanNorm z * |clockCovarianceKernel Q z|‖ ≤ r₀ * |clockCovarianceKernel Q z| := by
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (show 0 ≤ euclideanNorm z from Real.sqrt_nonneg _), abs_abs]
  by_cases hz : euclideanNorm z ≤ r₀
  · exact mul_le_mul_of_nonneg_right hz (abs_nonneg _)
  · rw [clockCovarianceKernel_eq_zero Q z (lt_of_not_ge hz), abs_zero, mul_zero,
      mul_zero]

/-- The first Euclidean covariance moment is genuinely integrable. -/
theorem integrable_clockCovarianceKernel_moment (Q : EnvironmentLaw d Λ₀ r₀) :
    Integrable (fun z => euclideanNorm z * |clockCovarianceKernel Q z|) := by
  apply ((integrable_clockCovarianceKernel Q).abs.const_mul r₀).mono'
    ((by
      unfold euclideanNorm euclideanSq dot
      fun_prop : Measurable (fun z : Vec d => euclideanNorm z)).mul
      (continuous_abs.measurable.comp (measurable_clockCovarianceKernel Q))).aestronglyMeasurable
  exact ae_of_all _ (clockKernel_moment_bound Q)

/-- Its first moment is bounded with the same structural variance constant. -/
theorem integral_clockCovarianceKernel_moment_le (Q : EnvironmentLaw d Λ₀ r₀) :
    (∫ z, euclideanNorm z * |clockCovarianceKernel Q z|) ≤
      r₀ * clockVarianceConstant d Λ₀ r₀ := by
  calc
    _ ≤ ∫ z, r₀ * |clockCovarianceKernel Q z| :=
      integral_mono (integrable_clockCovarianceKernel_moment Q)
        ((integrable_clockCovarianceKernel Q).abs.const_mul r₀) fun z =>
          (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using!
            clockKernel_moment_bound Q z)
    _ = r₀ * ∫ z, |clockCovarianceKernel Q z| := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (integral_abs_clockCovarianceKernel_le Q)
      (zero_le_one.trans Q.range_parameter)

private theorem integrable_clockCovariance_bilinear (Q : EnvironmentLaw d Λ₀ r₀)
    {f g : Vec d → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : Integrable f) (hg : Integrable g) :
    Integrable (fun p : Vec d × Vec d =>
      f p.1 * g p.2 * clockCovariance Q p.1 p.2) := by
  apply ((hf.norm.mul_prod hg.norm).mul_const ((2 * sourceReducedBound Λ₀) ^ 2)).mono'
    (((hfm.comp measurable_fst).fun_mul (hgm.comp measurable_snd)).fun_mul
      (measurable_clockCovariance Q)).aestronglyMeasurable
  exact ae_of_all _ fun p => by
    rw [norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left
      (by simpa only [Real.norm_eq_abs] using! abs_clockCovariance_le Q p.1 p.2)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- Absolute integrability of the displacement convolution is constructed by
the measure-preserving shear, before exchanging the spatial integrals. -/
theorem integrable_clockCovariance_convolution (Q : EnvironmentLaw d Λ₀ r₀)
    {f g : Vec d → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : Integrable f) (hg : Integrable g) :
    Integrable (fun p : Vec d × Vec d =>
      f p.1 * g (p.1 + p.2) * clockCovarianceKernel Q p.2) := by
  have hh := integrable_clockCovariance_bilinear Q hfm hgm hf hg
  change Integrable _ ((volume : Measure (Vec d)).prod volume) at hh ⊢
  have hi := (measurePreserving_prod_add volume volume).integrable_comp_of_integrable hh
  convert hi using 1
  funext p
  dsimp only [Function.comp_apply, Pi.mul_apply]
  rw [clockCovariance_eq_kernel, show p.1 - (p.1 + p.2) = -p.2 by abel,
    clockCovarianceKernel_neg]

/-- Exact bilinear convolution identity for the actual clock and real L1 tests. -/
theorem integral_clockTest_mul_eq_convolution (Q : EnvironmentLaw d Λ₀ r₀)
    {f g : Vec d → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : Integrable f) (hg : Integrable g) :
    (∫ ω, clockTest Q f ω * clockTest Q g ω ∂reducedLaw Q) =
      ∫ z, clockCovarianceKernel Q z * ∫ x, f x * g (x + z) := by
  rw [integral_clockTest_mul Q hfm hgm hf hg]
  calc
    _ = ∫ p : Vec d × Vec d,
        f p.1 * g (p.1 + p.2) * clockCovarianceKernel Q p.2 := by
      change (∫ p, f p.1 * g p.2 * clockCovariance Q p.1 p.2
        ∂(volume : Measure (Vec d)).prod volume) = _
      rw [← (measurePreserving_prod_add (volume : Measure (Vec d)) volume).integral_comp
        (MeasurableEquiv.shearAddRight (Vec d)).measurableEmbedding
        (fun p => f p.1 * g p.2 * clockCovariance Q p.1 p.2)]
      apply integral_congr_ae
      exact ae_of_all _ fun p => by
        dsimp only
        rw [clockCovariance_eq_kernel, show p.1 - (p.1 + p.2) = -p.2 by abel,
          clockCovarianceKernel_neg]
    _ = ∫ z, ∫ x, f x * g (x + z) * clockCovarianceKernel Q z :=
      integral_prod_symm _ (integrable_clockCovariance_convolution Q hfm hgm hf hg)
    _ = _ := by
      simp_rw [integral_mul_const, mul_comm (clockCovarianceKernel Q _)]

/-- The exact rescaling in spatial dimension d. The normalization equals the
product of the two source factors R^(-d/2). -/
theorem clockCovariance_rescaled_convolution (Q : EnvironmentLaw d Λ₀ r₀)
    {f g : Vec d → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : Integrable f) (hg : Integrable g) {R : ℝ} (hR : 0 < R) :
    (R ^ d)⁻¹ * (∫ ω,
      clockTest Q (fun x => f (R⁻¹ • x)) ω *
        clockTest Q (fun x => g (R⁻¹ • x)) ω ∂reducedLaw Q) =
      ∫ z, clockCovarianceKernel Q z * ∫ x, f x * g (x + R⁻¹ • z) := by
  rw [integral_clockTest_mul_eq_convolution Q
    (f := fun x => f (R⁻¹ • x)) (g := fun x => g (R⁻¹ • x))
    (hfm.comp (measurable_id.const_smul R⁻¹))
    (hgm.comp (measurable_id.const_smul R⁻¹))
    (hf.comp_smul (inv_ne_zero hR.ne')) (hg.comp_smul (inv_ne_zero hR.ne'))]
  have he (z : Vec d) :
      (∫ x, f (R⁻¹ • x) * g (R⁻¹ • (x + z))) =
        R ^ d * ∫ x, f x * g (x + R⁻¹ • z) := by
    simp_rw [smul_add]
    simpa only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin, mul_one,
      smul_eq_mul] using
      Measure.integral_comp_inv_smul_of_nonneg (volume : Measure (Vec d))
        (fun x => f x * g (x + R⁻¹ • z)) hR.le
  simp_rw [he]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun z => by field_simp

private theorem integrable_mul_of_bounded {f g : Vec d → ℝ}
    (hf : Integrable f) (hgm : Measurable g) {B : ℝ} (hB : ∀ x, |g x| ≤ B) :
    Integrable (fun x => f x * g x) := by
  exact (hf.norm.mul_const B).mono'
    (hf.aestronglyMeasurable.mul hgm.aestronglyMeasurable) (ae_of_all _ fun x => by
      rw [norm_mul, Real.norm_eq_abs (g x)]
      exact mul_le_mul_of_nonneg_left (hB x) (norm_nonneg _))

/-- Deterministic translation error, with genuine regularity hypotheses.
The spatial test f is only L1; the actual covariance is not a premise. -/
theorem clockTest_translation_error_le {f g : Vec d → ℝ} (hf : Integrable f)
    (hgm : Measurable g) {B A : ℝ} (hB : ∀ x, |g x| ≤ B)
    (hA : ∀ x z, |g (x + z) - g x| ≤ A * euclideanNorm z) (z : Vec d) :
    |(∫ x, f x * g (x + z)) - ∫ x, f x * g x| ≤
      A * euclideanNorm z * ∫ x, |f x| := by
  have hg : Integrable (fun x => f x * g x) := integrable_mul_of_bounded hf hgm hB
  have hgz : Integrable (fun x => f x * g (x + z)) :=
    integrable_mul_of_bounded hf (hgm.comp (measurable_id.add_const z)) (fun x => hB _)
  calc
    _ = |∫ x, f x * (g (x + z) - g x)| := by
      rw [← integral_sub hgz hg]
      simp_rw [mul_sub]
    _ ≤ ∫ x, |f x * (g (x + z) - g x)| := abs_integral_le_integral_abs
    _ ≤ ∫ x, A * euclideanNorm z * |f x| := by
      apply integral_mono
      · simpa only [mul_sub] using! (hgz.sub hg).abs
      · exact hf.abs.const_mul _
      · intro x
        dsimp only
        rw [abs_mul, mul_comm (A * euclideanNorm z)]
        exact mul_le_mul_of_nonneg_left (hA x z) (abs_nonneg _)
    _ = _ := integral_const_mul _ _

private theorem clockCorrelation_abs_le {f g : Vec d → ℝ} (hf : Integrable f)
    (hgm : Measurable g) {B : ℝ} (hB : ∀ x, |g x| ≤ B) (z : Vec d) :
    |∫ x, f x * g (x + z)| ≤ B * ∫ x, |f x| := by
  calc
    _ ≤ ∫ x, |f x * g (x + z)| := abs_integral_le_integral_abs
    _ ≤ ∫ x, B * |f x| := by
      apply integral_mono (integrable_mul_of_bounded hf
        (hgm.comp (measurable_id.add_const z)) (fun x => hB _)).abs (hf.abs.const_mul B)
      intro x
      dsimp only
      rw [abs_mul, mul_comm B]
      exact mul_le_mul_of_nonneg_left (hB _) (abs_nonneg _)
    _ = _ := integral_const_mul _ _

private theorem euclideanNorm_nonneg_smul (a : ℝ) (ha : 0 ≤ a) (z : Vec d) :
    euclideanNorm (a • z) = a * euclideanNorm z := by
  have he : euclideanSq (a • z) = a ^ 2 * euclideanSq z := by
    simp only [euclideanSq, dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [euclideanNorm, he, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha]
  rfl

/-- Quantitative covariance convergence for real integrable tests with a
bounded, Euclidean Lipschitz second test. All error terms are derived from the
actual clock kernel; the coefficient is uniform in the environment. -/
theorem clockCovariance_rescaled_error_le (Q : EnvironmentLaw d Λ₀ r₀)
    {f g : Vec d → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : Integrable f) (hg : Integrable g) {B A : ℝ} (hAnonneg : 0 ≤ A)
    (hB : ∀ x, |g x| ≤ B)
    (hA : ∀ x z, |g (x + z) - g x| ≤ A * euclideanNorm z)
    {R : ℝ} (hR : 0 < R) :
    |(R ^ d)⁻¹ * (∫ ω,
      clockTest Q (fun x => f (R⁻¹ • x)) ω *
        clockTest Q (fun x => g (R⁻¹ • x)) ω ∂reducedLaw Q) -
      clockCovarianceLimit Q * ∫ x, f x * g x| ≤
        r₀ * clockVarianceConstant d Λ₀ r₀ * A * (∫ x, |f x|) * R⁻¹ := by
  rw [clockCovariance_rescaled_convolution Q hfm hgm hf hg hR]
  have hm : Measurable (fun z : Vec d => ∫ x, f x * g (x + R⁻¹ • z)) :=
    (((hfm.comp measurable_snd).fun_mul (hgm.comp (measurable_snd.fun_add
      (measurable_fst.const_smul R⁻¹)))).stronglyMeasurable.integral_prod_right').measurable
  have hi : Integrable (fun z => clockCovarianceKernel Q z *
      ∫ x, f x * g (x + R⁻¹ • z)) := by
    apply ((integrable_clockCovarianceKernel Q).abs.mul_const (B * ∫ x, |f x|)).mono'
      ((measurable_clockCovarianceKernel Q).fun_mul hm).aestronglyMeasurable
    exact ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (clockCorrelation_abs_le hf hgm hB _) (abs_nonneg _)
  have hi₀ := (integrable_clockCovarianceKernel Q).mul_const (∫ x, f x * g x)
  have hI : 0 ≤ ∫ x, |f x| := integral_nonneg fun _ => abs_nonneg _
  have hbound (z : Vec d) :
      |clockCovarianceKernel Q z * ((∫ x, f x * g (x + R⁻¹ • z)) - ∫ x, f x * g x)| ≤
        (euclideanNorm z * |clockCovarianceKernel Q z|) * (A * (∫ x, |f x|) * R⁻¹) := by
    rw [abs_mul]
    have ht := clockTest_translation_error_le hf hgm hB hA (R⁻¹ • z)
    rw [euclideanNorm_nonneg_smul _ (inv_nonneg.mpr hR.le)] at ht
    calc
      _ ≤ |clockCovarianceKernel Q z| * (A * (R⁻¹ * euclideanNorm z) * ∫ x, |f x|) :=
        mul_le_mul_of_nonneg_left ht (abs_nonneg _)
      _ = _ := by ring
  calc
    _ = |∫ z, clockCovarianceKernel Q z *
        ((∫ x, f x * g (x + R⁻¹ • z)) - ∫ x, f x * g x)| := by
      rw [clockCovarianceLimit, ← integral_mul_const, ← integral_sub hi hi₀]
      simp_rw [mul_sub]
    _ ≤ ∫ z, |clockCovarianceKernel Q z *
        ((∫ x, f x * g (x + R⁻¹ • z)) - ∫ x, f x * g x)| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ z, (euclideanNorm z * |clockCovarianceKernel Q z|) *
        (A * (∫ x, |f x|) * R⁻¹) := by
      apply integral_mono
      · simpa only [mul_sub] using! (hi.sub hi₀).abs
      · exact (integrable_clockCovarianceKernel_moment Q).mul_const _
      · exact hbound
    _ = (∫ z, euclideanNorm z * |clockCovarianceKernel Q z|) *
        (A * (∫ x, |f x|) * R⁻¹) := integral_mul_const _ _
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_right (integral_clockCovarianceKernel_moment_le Q)
        (mul_nonneg (mul_nonneg hAnonneg hI) (inv_nonneg.mpr hR.le))
      convert h using 1
      ring

private theorem clockLimit_norm_le_euclidean (x : Vec d) : ‖x‖ ≤ euclideanNorm x := by
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
  intro i
  rw [Real.norm_eq_abs]
  apply Real.abs_le_sqrt
  change x i ^ 2 ≤ ∑ j, x j * x j
  simpa only [pow_two] using! Finset.single_le_sum
    (fun j _ => mul_self_nonneg (x j)) (Finset.mem_univ i)

private def clockLimitTent (x : Vec d) : ℝ := max (-‖x‖ + 1) 0

private theorem clockLimitTent_lipschitz : LipschitzWith 1 (clockLimitTent (d := d)) := by
  change LipschitzWith 1 (fun x : Vec d => max (-‖x‖ + 1) 0)
  simpa only [zero_add, sub_eq_add_neg, add_comm] using!
    ((LipschitzWith.const (1 : ℝ)).sub (lipschitzWith_one_norm (E := Vec d))).max_const 0

private theorem clockLimitTent_compact : HasCompactSupport (clockLimitTent (d := d)) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Vec d) 1)
  intro x hx
  have hnorm : 1 < ‖x‖ := by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using! hx
  exact max_eq_right (by linarith)

private theorem clockLimitTent_integrable : Integrable (clockLimitTent (d := d)) :=
  clockLimitTent_lipschitz.continuous.integrable_of_hasCompactSupport clockLimitTent_compact

/-- Positivity is obtained as a limit of actual clock variances. No positivity
of the pointwise covariance kernel is asserted or assumed. -/
theorem clockCovarianceLimit_nonneg (Q : EnvironmentLaw d Λ₀ r₀) :
    0 ≤ clockCovarianceLimit Q := by
  let f : Vec d → ℝ := clockLimitTent
  have hfc : Continuous f := clockLimitTent_lipschitz.continuous
  have hfi : Integrable f := clockLimitTent_integrable
  have hfB (x : Vec d) : |f x| ≤ 1 := by
    dsimp only [f, clockLimitTent]
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith [norm_nonneg x]) zero_le_one
  have hfA (x z : Vec d) : |f (x + z) - f x| ≤ 1 * euclideanNorm z := by
    have h := clockLimitTent_lipschitz.dist_le_mul (x + z) x
    rw [Real.dist_eq, dist_eq_norm, add_sub_cancel_left, NNReal.coe_one, one_mul] at h
    exact h.trans (by simpa only [one_mul] using! clockLimit_norm_le_euclidean z)
  have hf2i : Integrable (fun x => f x * f x) :=
    integrable_mul_of_bounded hfi hfc.measurable hfB
  have hI : 0 < ∫ x, f x * f x :=
    integral_pos_of_integrable_nonneg_nonzero (hfc.mul hfc) hf2i
      (fun _ => mul_self_nonneg _) (x := 0) (by norm_num [f, clockLimitTent])
  let C := r₀ * clockVarianceConstant d Λ₀ r₀ * 1 * (∫ x, |f x|)
  have hlim : Filter.Tendsto (fun R : ℝ => -(C * R⁻¹)) Filter.atTop (nhds 0) := by
    simpa only [mul_zero, neg_zero] using!
      ((tendsto_const_nhds (x := C)).mul tendsto_inv_atTop_zero).neg
  have hnonneg : 0 ≤ clockCovarianceLimit Q * ∫ x, f x * f x := by
    apply le_of_tendsto hlim
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with R hR
    have he := clockCovariance_rescaled_error_le Q hfc.measurable hfc.measurable
      hfi hfi zero_le_one hfB hfA hR
    have hv : 0 ≤ (R ^ d)⁻¹ * (∫ ω,
        clockTest Q (fun x => f (R⁻¹ • x)) ω *
          clockTest Q (fun x => f (R⁻¹ • x)) ω ∂reducedLaw Q) :=
      mul_nonneg (inv_nonneg.mpr (pow_nonneg hR.le _))
        (integral_nonneg fun _ => mul_self_nonneg _)
    have hlo := (abs_le.mp he).2
    dsimp only [C]
    linarith
  exact nonneg_of_mul_nonneg_left hnonneg hI

private def clockLimitBilinear (Q : EnvironmentLaw d Λ₀ r₀) :
    Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q) →L[ℂ] ℂ :=
  (ContinuousLinearMap.mul ℂ ℂ).lpPairing (reducedLaw Q) 2 2

private theorem clockLimitBilinear_eq (Q : EnvironmentLaw d Λ₀ r₀)
    (u v : Lp ℂ 2 (reducedLaw Q)) :
    clockLimitBilinear Q u v = ∫ ω, u ω * v ω ∂reducedLaw Q :=
  ContinuousLinearMap.lpPairing_eq_integral _ _ _

private theorem clockLimit_translation_ae (Q : EnvironmentLaw d Λ₀ r₀)
    {u : Lp ℂ 2 (reducedLaw Q)}
    (hu : (u : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
      fun ω => (centeredClockField Q 0 ω : ℂ)) (x : Vec d) :
    (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x u : FieldPair d → ℂ)
      =ᵐ[reducedLaw Q] fun ω => (centeredClockField Q x ω : ℂ) := by
  have hp := (measurePreserving_translate (reducedLaw Q) (reducedLaw_stationary Q) x).quasiMeasurePreserving.ae hu
  filter_upwards [coeFn_complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x u,
    hp] with ω hω hω'
  rw [hω, hω']
  simp only [centeredClockField, translate_scalar, add_zero]

/-- Bilinear covariance of any L2 representative of the actual centered clock.
Both translated observations use the same reduced joint law. -/
theorem integral_translated_clock_mul (Q : EnvironmentLaw d Λ₀ r₀)
    {u : Lp ℂ 2 (reducedLaw Q)}
    (hu : (u : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
      fun ω => (centeredClockField Q 0 ω : ℂ)) (x y : Vec d) :
    (∫ ω, complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x u ω *
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y u ω ∂reducedLaw Q) =
        (clockCovariance Q x y : ℂ) := by
  rw [clockCovariance, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [clockLimit_translation_ae Q hu x, clockLimit_translation_ae Q hu y]
    with ω hx hy
  rw [hx, hy, Complex.ofReal_mul]

/-- The actual complex clock spatial integral, in reduced-law L2. -/
noncomputable def complexClockSpatialPairing (Q : EnvironmentLaw d Λ₀ r₀)
    (u : Lp ℂ 2 (reducedLaw Q)) (f : Vec d → ℂ) : Lp ℂ 2 (reducedLaw Q) :=
  ∫ x, f x • complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x u

/-- Exact complex bilinear covariance formula for the literal Bochner integral.
The integrability of each L2 orbit is supplied by the stationary isometry. -/
theorem integral_complexClockSpatialPairing_mul (Q : EnvironmentLaw d Λ₀ r₀)
    {u : Lp ℂ 2 (reducedLaw Q)}
    (hu : (u : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
      fun ω => (centeredClockField Q 0 ω : ℂ))
    {f g : Vec d → ℂ} (hfc : Continuous f) (hgc : Continuous g)
    (hf : Integrable f) (hg : Integrable g) :
    (∫ ω, complexClockSpatialPairing Q u f ω * complexClockSpatialPairing Q u g ω
      ∂reducedLaw Q) = ∫ x, ∫ y, f x * g y * (clockCovariance Q x y : ℂ) := by
  letI := reducedLaw_probability Q
  have hfi := integrable_kernel_complexTranslation (reducedLaw Q) (reducedLaw_stationary Q)
    f hf hfc u
  have hgi := integrable_kernel_complexTranslation (reducedLaw Q) (reducedLaw_stationary Q)
    g hg hgc u
  let T (x : Vec d) := complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x u
  let B := clockLimitBilinear Q
  rw [← clockLimitBilinear_eq]
  change B (∫ x, f x • T x) (∫ y, g y • T y) = _
  calc
    _ = ∫ x, B (f x • T x) (∫ y, g y • T y) :=
      ((B.flip (∫ y, g y • T y)).integral_comp_comm hfi).symm
    _ = ∫ x, ∫ y, B (f x • T x) (g y • T y) := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => ((B (f x • T x)).integral_comp_comm hgi).symm
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by
        apply integral_congr_ae
        exact ae_of_all _ fun y => by
          have hb : B (f x • T x) (g y • T y) =
              f x * (g y * B (T x) (T y)) := by
            rw [ContinuousLinearMap.map_smul₂, map_smul, smul_eq_mul, smul_eq_mul]
          change B (f x • T x) (g y • T y) = _
          rw [hb, clockLimitBilinear_eq, integral_translated_clock_mul Q hu]
          exact (mul_assoc _ _ _).symm

private theorem integrable_complex_clockCovariance_bilinear (Q : EnvironmentLaw d Λ₀ r₀)
    {f g : Vec d → ℂ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : Integrable f) (hg : Integrable g) :
    Integrable (fun p : Vec d × Vec d =>
      f p.1 * g p.2 * (clockCovariance Q p.1 p.2 : ℂ)) := by
  apply ((hf.norm.mul_prod hg.norm).mul_const ((2 * sourceReducedBound Λ₀) ^ 2)).mono'
    (((hfm.comp measurable_fst).fun_mul (hgm.comp measurable_snd)).mul
      (Complex.measurable_ofReal.comp (measurable_clockCovariance Q))).aestronglyMeasurable
  exact ae_of_all _ fun p => by
    dsimp only [Function.comp_apply, Pi.mul_apply]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (abs_clockCovariance_le Q p.1 p.2)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- The complex version of the displacement convolution formula preserves the
bilinear convention: no conjugate is inserted. -/
theorem integral_complexClockSpatialPairing_mul_eq_convolution
    (Q : EnvironmentLaw d Λ₀ r₀) {u : Lp ℂ 2 (reducedLaw Q)}
    (hu : (u : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
      fun ω => (centeredClockField Q 0 ω : ℂ))
    {f g : Vec d → ℂ} (hfc : Continuous f) (hgc : Continuous g)
    (hf : Integrable f) (hg : Integrable g) :
    (∫ ω, complexClockSpatialPairing Q u f ω * complexClockSpatialPairing Q u g ω
      ∂reducedLaw Q) = ∫ z, (clockCovarianceKernel Q z : ℂ) * ∫ x, f x * g (x + z) := by
  have hh := integrable_complex_clockCovariance_bilinear Q hfc.measurable hgc.measurable hf hg
  change Integrable _ ((volume : Measure (Vec d)).prod volume) at hh
  have he (p : Vec d × Vec d) :
      f p.1 * g (p.1 + p.2) * (clockCovariance Q p.1 (p.1 + p.2) : ℂ) =
        f p.1 * g (p.1 + p.2) * (clockCovarianceKernel Q p.2 : ℂ) := by
    rw [clockCovariance_eq_kernel, show p.1 - (p.1 + p.2) = -p.2 by abel,
      clockCovarianceKernel_neg]
  have hi := (measurePreserving_prod_add volume volume).integrable_comp_of_integrable hh
  change Integrable (fun p : Vec d × Vec d => f p.1 * g (p.1 + p.2) *
    (clockCovariance Q p.1 (p.1 + p.2) : ℂ)) (volume.prod volume) at hi
  simp_rw [he] at hi
  rw [integral_complexClockSpatialPairing_mul Q hu hfc hgc hf hg, ← integral_prod _ hh,
    ← (measurePreserving_prod_add (volume : Measure (Vec d)) volume).integral_comp
      (MeasurableEquiv.shearAddRight (Vec d)).measurableEmbedding
      (fun p => f p.1 * g p.2 * (clockCovariance Q p.1 p.2 : ℂ))]
  simp_rw [he]
  rw [integral_prod_symm _ hi]
  simp_rw [integral_mul_const, mul_comm (clockCovarianceKernel Q _ : ℂ)]

/-- The clock restriction of the source R^(-d/2) Bochner spatial integral. -/
noncomputable def scaledComplexClockPairing (Q : EnvironmentLaw d Λ₀ r₀)
    (R : ℝ) (u : Lp ℂ 2 (reducedLaw Q)) (f : Vec d → ℂ) : Lp ℂ 2 (reducedLaw Q) :=
  ((R ^ (-(d : ℝ) / 2) : ℝ) : ℂ) •
    complexClockSpatialPairing Q u (fun x => f (R⁻¹ • x))

private theorem clockScale_sq {R : ℝ} (hR : 0 < R) :
    R ^ (-(d : ℝ) / 2) * R ^ (-(d : ℝ) / 2) = (R ^ d)⁻¹ := by
  rw [← Real.rpow_add hR, show -(d : ℝ) / 2 + -(d : ℝ) / 2 = -(d : ℝ) by ring,
    Real.rpow_neg hR.le, Real.rpow_natCast]

/-- Exact rescaled complex bilinear convolution, with the frozen Euclidean
dimension normalization and a single law-dependent displacement kernel. -/
theorem scaledComplexClockPairing_covariance (Q : EnvironmentLaw d Λ₀ r₀)
    {u : Lp ℂ 2 (reducedLaw Q)}
    (hu : (u : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
      fun ω => (centeredClockField Q 0 ω : ℂ))
    {f g : Vec d → ℂ} (hfc : Continuous f) (hgc : Continuous g)
    (hf : Integrable f) (hg : Integrable g) {R : ℝ} (hR : 0 < R) :
    (∫ ω, scaledComplexClockPairing Q R u f ω * scaledComplexClockPairing Q R u g ω
      ∂reducedLaw Q) = ∫ z, (clockCovarianceKernel Q z : ℂ) *
        ∫ x, f x * g (x + R⁻¹ • z) := by
  rw [← clockLimitBilinear_eq, scaledComplexClockPairing, scaledComplexClockPairing,
    map_smul, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, smul_eq_mul,
    ← mul_assoc, ← Complex.ofReal_mul, clockScale_sq hR, clockLimitBilinear_eq]
  rw [integral_complexClockSpatialPairing_mul_eq_convolution Q hu
    (f := fun x => f (R⁻¹ • x)) (g := fun x => g (R⁻¹ • x))
    (hfc.comp (continuous_id.const_smul R⁻¹))
    (hgc.comp (continuous_id.const_smul R⁻¹))
    (hf.comp_smul (inv_ne_zero hR.ne')) (hg.comp_smul (inv_ne_zero hR.ne'))]
  have he (z : Vec d) :
      (∫ x, f (R⁻¹ • x) * g (R⁻¹ • (x + z))) =
        (R ^ d : ℝ) • ∫ x, f x * g (x + R⁻¹ • z) := by
    simp_rw [smul_add]
    simpa only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin, mul_one] using!
      Measure.integral_comp_inv_smul_of_nonneg (volume : Measure (Vec d))
        (fun x => f x * g (x + R⁻¹ • z)) hR.le
  simp_rw [he, Complex.real_smul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun z => by
    rw [Complex.ofReal_inv]
    have hp : (R ^ d : ℂ) ≠ 0 := by exact_mod_cast pow_ne_zero d hR.ne'
    field_simp [hp, show (↑(R ^ d) : ℂ) ≠ 0 by exact_mod_cast pow_ne_zero d hR.ne']

/-- A literal consumer of the frozen joint integral, restricted to tests whose
commutator coordinates vanish. The last coordinate is the actual clock. -/
theorem scaledJointPairing_eq_clock (Q : EnvironmentLaw d Λ₀ r₀)
    (R : ℝ) (hR : 0 < R) (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q))
    (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)))
    (hF : ∀ x j i, F x (.inl (j, i)) = 0) :
    scaledJointPairing Q R hR Z F =
      scaledComplexClockPairing Q R (Z (.inr ())) (fun x => F x (.inr ())) := by
  unfold scaledJointPairing scaledComplexClockPairing complexClockSpatialPairing
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    simp only [Fintype.sum_sum_type, hF, zero_smul,
      Finset.sum_const_zero, Fintype.sum_unique, zero_add]

/-- Exact clock-only restriction of the covariance in the frozen joint
statement. It applies to every actual joint-field realization Z. -/
theorem scaledJointPairing_clock_covariance (Q : EnvironmentLaw d Λ₀ r₀)
    (R : ℝ) (hR : 0 < R) (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q))
    (hZ : IsJointObservation Q Z)
    (F G : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)))
    (hF : ∀ x j i, F x (.inl (j, i)) = 0)
    (hG : ∀ x j i, G x (.inl (j, i)) = 0) :
    (∫ ω, scaledJointPairing Q R hR Z F ω * scaledJointPairing Q R hR Z G ω
      ∂reducedLaw Q) = ∫ z, (clockCovarianceKernel Q z : ℂ) *
        ∫ x, F x (.inr ()) * G (x + R⁻¹ • z) (.inr ()) := by
  rw [scaledJointPairing_eq_clock Q R hR Z F hF, scaledJointPairing_eq_clock Q R hR Z G hG]
  have hc (H : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))) :
      Continuous (fun x => H x (.inr ())) :=
    (PiLp.continuous_apply 2 _ (Sum.inr () : JointObservationIndex d)).comp H.continuous
  have hi (H : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))) :
      Integrable (fun x => H x (.inr ())) :=
    H.integrable.mono (hc H).aestronglyMeasurable
      (ae_of_all _ fun x => PiLp.norm_apply_le (H x) _)
  exact scaledComplexClockPairing_covariance Q hZ.2 (hc F) (hc G) (hi F) (hi G) hR

/-- The prescribed finite Schwartz norm bounds its zero-order weighted value. -/
theorem clockSchwartz_weighted_value_le (N : ℕ)
    (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))) (x : Vec d) :
    (1 + euclideanNorm x) ^ N * ‖F x‖ ≤ schwartzTestNorm N F := by
  apply le_csSup (schwartzTestNorm_set_bddAbove N F)
  exact ⟨⟨0, by omega⟩, Fin.elim0, x, by simp only [iteratedFDeriv_zero_apply]⟩

/-- Nonnegativity of the literal source test norm. -/
theorem clockSchwartz_norm_nonneg (N : ℕ)
    (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))) :
    0 ≤ schwartzTestNorm N F :=
  (mul_nonneg (pow_nonneg (show 0 ≤ 1 + euclideanNorm (0 : Vec d) from by
    exact add_nonneg zero_le_one (Real.sqrt_nonneg _)) N) (norm_nonneg (F 0))).trans
    (clockSchwartz_weighted_value_le N F 0)

/-- The same norm controls every first coordinate partial derivative. -/
theorem clockSchwartz_partial_le {N : ℕ} (hN : 1 ≤ N)
    (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)))
    (x : Vec d) (j : Fin d) :
    ‖fderiv ℝ (fun y => F y) x (unitVector j)‖ ≤ schwartzTestNorm N F := by
  have h : (1 + euclideanNorm x) ^ N *
      ‖fderiv ℝ (fun y => F y) x (unitVector j)‖ ≤ schwartzTestNorm N F := by
    apply le_csSup (schwartzTestNorm_set_bddAbove N F)
    exact ⟨⟨1, by omega⟩, (fun _ => j), x, by simp only [iteratedFDeriv_one_apply]⟩
  have hw : 1 ≤ (1 + euclideanNorm x) ^ N := one_le_pow₀ (show 1 ≤ 1 + euclideanNorm x from le_add_of_nonneg_right (Real.sqrt_nonneg _))
  exact (le_mul_of_one_le_left (norm_nonneg _) hw).trans h

private theorem clockSchwartz_value_le (N : ℕ)
    (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))) (x : Vec d) :
    ‖F x‖ ≤ schwartzTestNorm N F := by
  exact (le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ (show 1 ≤ 1 + euclideanNorm x from le_add_of_nonneg_right (Real.sqrt_nonneg _)))).trans
    (clockSchwartz_weighted_value_le N F x)

private theorem clockSchwartz_fderiv_le {N : ℕ} (hN : 1 ≤ N)
    (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))) (x : Vec d) :
    ‖fderiv ℝ (fun y => F y) x‖ ≤ d * schwartzTestNorm N F := by
  classical
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Nat.cast_nonneg _) (clockSchwartz_norm_nonneg N F))
  intro z
  have hz : z = ∑ j : Fin d, z j • unitVector j := by
    ext i
    simp [unitVector, Finset.sum_apply, Pi.single_apply, Pi.smul_apply, smul_eq_mul]
  calc
    _ = ‖∑ j : Fin d, z j • fderiv ℝ (fun y => F y) x (unitVector j)‖ := by
      conv_lhs => rw [hz, map_sum]
      simp_rw [map_smul]
    _ ≤ ∑ j : Fin d, ‖z j • fderiv ℝ (fun y => F y) x (unitVector j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin d, ‖z‖ * schwartzTestNorm N F := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_smul]
      exact mul_le_mul (norm_le_pi_norm z j) (clockSchwartz_partial_le hN F x j)
        (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- A Euclidean translation estimate in exactly the frozen test norm. -/
theorem clockSchwartz_translation_le {N : ℕ} (hN : 1 ≤ N)
    (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))) (x z : Vec d) :
    ‖F (x + z) - F x‖ ≤ d * schwartzTestNorm N F * euclideanNorm z := by
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le (s := Set.univ)
    (fun y _ => (F.smooth (1 : ℕ)).differentiable (by norm_num) y)
    (fun y _ => clockSchwartz_fderiv_le hN F y) convex_univ
    (Set.mem_univ x) (Set.mem_univ (x + z))
  rw [add_sub_cancel_left] at h
  exact h.trans (mul_le_mul_of_nonneg_left (clockLimit_norm_le_euclidean z)
    (mul_nonneg (Nat.cast_nonneg _) (clockSchwartz_norm_nonneg N F)))

/-- A structural spatial weight mass for the fixed source test order. -/
noncomputable def clockSchwartzWeightMass (d N : ℕ) : ℝ :=
  ∫ x : Vec d, (1 + ‖x‖) ^ (-(N : ℝ))

/-- The weight is integrable at the source order, without choosing a test. -/
theorem integrable_clockSchwartzWeight {N : ℕ} (hN : d < N) :
    Integrable (fun x : Vec d => (1 + ‖x‖) ^ (-(N : ℝ))) := by
  apply integrable_one_add_norm
  simpa only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin, mul_one] using!
    (show (d : ℝ) < N by exact_mod_cast hN)

/-- L1 contraction in the prescribed finite weighted norm, with structural
constant chosen before the test and the law. -/
theorem clockSchwartz_integral_norm_le {N : ℕ} (hN : d < N)
    (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))) :
    (∫ x, ‖F x‖) ≤ clockSchwartzWeightMass d N * schwartzTestNorm N F := by
  have hb (x : Vec d) : ‖F x‖ ≤
      (1 + ‖x‖) ^ (-(N : ℝ)) * schwartzTestNorm N F := by
    rw [Real.rpow_neg (by positivity : 0 ≤ 1 + ‖x‖), Real.rpow_natCast,
      ← div_eq_inv_mul, le_div_iff₀' (by positivity)]
    calc
      _ ≤ (1 + euclideanNorm x) ^ N * ‖F x‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact pow_le_pow_left₀ (by positivity) (by linarith [clockLimit_norm_le_euclidean x]) N
      _ ≤ _ := clockSchwartz_weighted_value_le N F x
  calc
    _ ≤ ∫ x, (1 + ‖x‖) ^ (-(N : ℝ)) * schwartzTestNorm N F :=
      integral_mono F.integrable.norm ((integrable_clockSchwartzWeight hN).mul_const _) hb
    _ = _ := integral_mul_const _ _

private theorem integrable_complex_mul_of_bounded {f g : Vec d → ℂ}
    (hf : Integrable f) (hgm : Measurable g) {B : ℝ} (hB : ∀ x, ‖g x‖ ≤ B) :
    Integrable (fun x => f x * g x) := by
  exact (hf.norm.mul_const B).mono'
    (hf.aestronglyMeasurable.mul hgm.aestronglyMeasurable) (ae_of_all _ fun x => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hB x) (norm_nonneg _))

private theorem complexClock_translation_error_le {f g : Vec d → ℂ} (hf : Integrable f)
    (hgm : Measurable g) {B A : ℝ} (hB : ∀ x, ‖g x‖ ≤ B)
    (hA : ∀ x z, ‖g (x + z) - g x‖ ≤ A * euclideanNorm z) (z : Vec d) :
    ‖(∫ x, f x * g (x + z)) - ∫ x, f x * g x‖ ≤
      A * euclideanNorm z * ∫ x, ‖f x‖ := by
  have hg := integrable_complex_mul_of_bounded hf hgm hB
  have hgz := integrable_complex_mul_of_bounded (g := fun x => g (x + z)) hf
    (hgm.comp (measurable_id.add_const z)) (fun x => hB (x + z))
  calc
    _ = ‖∫ x, f x * (g (x + z) - g x)‖ := by
      rw [← integral_sub hgz hg]
      simp_rw [mul_sub]
    _ ≤ ∫ x, ‖f x * (g (x + z) - g x)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, A * euclideanNorm z * ‖f x‖ := by
      apply integral_mono
      · simpa only [mul_sub] using! (hgz.sub hg).norm
      · exact hf.norm.const_mul _
      · intro x
        dsimp only
        rw [norm_mul, mul_comm (A * euclideanNorm z)]
        exact mul_le_mul_of_nonneg_left (hA x z) (norm_nonneg _)
    _ = _ := integral_const_mul _ _

private theorem complexClockCorrelation_norm_le {f g : Vec d → ℂ} (hf : Integrable f)
    (hgm : Measurable g) {B : ℝ} (hB : ∀ x, ‖g x‖ ≤ B) (z : Vec d) :
    ‖∫ x, f x * g (x + z)‖ ≤ B * ∫ x, ‖f x‖ := by
  calc
    _ ≤ ∫ x, ‖f x * g (x + z)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, B * ‖f x‖ := by
      apply integral_mono (integrable_complex_mul_of_bounded hf
        (hgm.comp (measurable_id.add_const z)) (fun x => hB _)).norm (hf.norm.const_mul B)
      intro x
      dsimp only
      rw [norm_mul, mul_comm B]
      exact mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _)
    _ = _ := integral_const_mul _ _

/-- The complex bilinear covariance rate for actual clock L2 integrals.
The deterministic regularity assumptions are discharged for the frozen
Schwartz tests below. -/
theorem scaledComplexClockPairing_error_le (Q : EnvironmentLaw d Λ₀ r₀)
    {u : Lp ℂ 2 (reducedLaw Q)}
    (hu : (u : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
      fun ω => (centeredClockField Q 0 ω : ℂ))
    {f g : Vec d → ℂ} (hfc : Continuous f) (hgc : Continuous g)
    (hf : Integrable f) (hg : Integrable g) {B A : ℝ} (hAnonneg : 0 ≤ A)
    (hB : ∀ x, ‖g x‖ ≤ B)
    (hA : ∀ x z, ‖g (x + z) - g x‖ ≤ A * euclideanNorm z)
    {R : ℝ} (hR : 0 < R) :
    ‖(∫ ω, scaledComplexClockPairing Q R u f ω * scaledComplexClockPairing Q R u g ω
      ∂reducedLaw Q) - (clockCovarianceLimit Q : ℂ) * ∫ x, f x * g x‖ ≤
        r₀ * clockVarianceConstant d Λ₀ r₀ * A * (∫ x, ‖f x‖) * R⁻¹ := by
  rw [scaledComplexClockPairing_covariance Q hu hfc hgc hf hg hR]
  have hm : Measurable (fun z : Vec d => ∫ x, f x * g (x + R⁻¹ • z)) :=
    (((hfc.measurable.comp measurable_snd).fun_mul (hgc.measurable.comp (measurable_snd.fun_add
      (measurable_fst.const_smul R⁻¹)))).stronglyMeasurable.integral_prod_right').measurable
  have hi : Integrable (fun z => (clockCovarianceKernel Q z : ℂ) *
      ∫ x, f x * g (x + R⁻¹ • z)) := by
    apply ((integrable_clockCovarianceKernel Q).abs.mul_const (B * ∫ x, ‖f x‖)).mono'
      ((Complex.measurable_ofReal.comp (measurable_clockCovarianceKernel Q)).mul hm).aestronglyMeasurable
    exact ae_of_all _ fun z => by
      dsimp only [Function.comp_apply, Pi.mul_apply]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (complexClockCorrelation_norm_le hf hgc.measurable hB _)
        (abs_nonneg _)
  have hi₀ : Integrable (fun z => (clockCovarianceKernel Q z : ℂ) * ∫ x, f x * g x) :=
    (integrable_clockCovarianceKernel Q).ofReal.mul_const _
  have hI : 0 ≤ ∫ x, ‖f x‖ := integral_nonneg fun _ => norm_nonneg _
  have hbound (z : Vec d) :
      ‖(clockCovarianceKernel Q z : ℂ) *
        ((∫ x, f x * g (x + R⁻¹ • z)) - ∫ x, f x * g x)‖ ≤
        (euclideanNorm z * |clockCovarianceKernel Q z|) * (A * (∫ x, ‖f x‖) * R⁻¹) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have ht := complexClock_translation_error_le hf hgc.measurable hB hA (R⁻¹ • z)
    rw [euclideanNorm_nonneg_smul _ (inv_nonneg.mpr hR.le)] at ht
    calc
      _ ≤ |clockCovarianceKernel Q z| * (A * (R⁻¹ * euclideanNorm z) * ∫ x, ‖f x‖) :=
        mul_le_mul_of_nonneg_left ht (abs_nonneg _)
      _ = _ := by ring
  calc
    _ = ‖∫ z, (clockCovarianceKernel Q z : ℂ) *
        ((∫ x, f x * g (x + R⁻¹ • z)) - ∫ x, f x * g x)‖ := by
      rw [clockCovarianceLimit, ← integral_complex_ofReal, ← integral_mul_const, ← integral_sub hi hi₀]
      simp_rw [mul_sub]
    _ ≤ ∫ z, ‖(clockCovarianceKernel Q z : ℂ) *
        ((∫ x, f x * g (x + R⁻¹ • z)) - ∫ x, f x * g x)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ z, (euclideanNorm z * |clockCovarianceKernel Q z|) *
        (A * (∫ x, ‖f x‖) * R⁻¹) := by
      apply integral_mono
      · simpa only [mul_sub] using! (hi.sub hi₀).norm
      · exact (integrable_clockCovarianceKernel_moment Q).mul_const _
      · exact hbound
    _ = (∫ z, euclideanNorm z * |clockCovarianceKernel Q z|) *
        (A * (∫ x, ‖f x‖) * R⁻¹) := integral_mul_const _ _
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_right (integral_clockCovarianceKernel_moment_le Q)
        (mul_nonneg (mul_nonneg hAnonneg hI) (inv_nonneg.mpr hR.le))
      convert h using 1
      ring

/-- Literal compact support of the measurable covariance, in addition to its
sharper Euclidean support statement. No continuity of the covariance is needed. -/
theorem hasCompactSupport_clockCovarianceKernel (Q : EnvironmentLaw d Λ₀ r₀) :
    HasCompactSupport (clockCovarianceKernel Q) := by
  apply HasCompactSupport.intro isCompact_Icc
  intro z hz
  have hm := abs_clockCovariance_le_majorant Q z 0
  have hz' : z - 0 ∉ Set.Icc (fun _ : Fin d => -r₀) (fun _ => r₀) := by
    simpa only [sub_zero] using! hz
  rw [clockCovarianceMajorant, Set.indicator_of_notMem hz'] at hm
  exact abs_nonpos_iff.mp hm

/-- The actual joint clock covariance converges at rate R⁻¹, in the exact
finite Schwartz norm prescribed by the frozen covariance statement. -/
theorem scaledJointPairing_clock_error_le (Q : EnvironmentLaw d Λ₀ r₀)
    {N : ℕ} (hN : d < N)
    (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q)) (hZ : IsJointObservation Q Z)
    {R : ℝ} (hR : 0 < R)
    (F G : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)))
    (hF : ∀ x j i, F x (.inl (j, i)) = 0)
    (hG : ∀ x j i, G x (.inl (j, i)) = 0) :
    ‖(∫ ω, scaledJointPairing Q R hR Z F ω * scaledJointPairing Q R hR Z G ω
      ∂reducedLaw Q) -
      ∫ x, F x (.inr ()) * (clockCovarianceLimit Q : ℂ) * G x (.inr ())‖ ≤
      (r₀ * clockVarianceConstant d Λ₀ r₀ * d * clockSchwartzWeightMass d N) *
        schwartzTestNorm N F * schwartzTestNorm N G * R⁻¹ := by
  have hc (H : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))) :
      Continuous (fun x => H x (.inr ())) :=
    (PiLp.continuous_apply 2 _ (Sum.inr () : JointObservationIndex d)).comp H.continuous
  have hi (H : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))) :
      Integrable (fun x => H x (.inr ())) :=
    H.integrable.mono (hc H).aestronglyMeasurable
      (ae_of_all _ fun x => PiLp.norm_apply_le (H x) _)
  have hg (x : Vec d) : ‖G x (.inr ())‖ ≤ schwartzTestNorm N G :=
    (PiLp.norm_apply_le (G x) _).trans (clockSchwartz_value_le N G x)
  have ht (x z : Vec d) :
      ‖G (x + z) (.inr ()) - G x (.inr ())‖ ≤
        (d * schwartzTestNorm N G) * euclideanNorm z :=
    (PiLp.norm_apply_le (G (x + z) - G x) (.inr ())).trans
      (clockSchwartz_translation_le (by omega) G x z)
  have hI : (∫ x, ‖F x (.inr ())‖) ≤
      clockSchwartzWeightMass d N * schwartzTestNorm N F :=
    (integral_mono (hi F).norm F.integrable.norm (fun x => PiLp.norm_apply_le (F x) _)).trans
      (clockSchwartz_integral_norm_le hN F)
  rw [scaledJointPairing_eq_clock Q R hR Z F hF,
    scaledJointPairing_eq_clock Q R hR Z G hG]
  have he : (∫ x, F x (.inr ()) * (clockCovarianceLimit Q : ℂ) * G x (.inr ())) =
      (clockCovarianceLimit Q : ℂ) * ∫ x, F x (.inr ()) * G x (.inr ()) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun _ => by ring
  rw [he]
  have h := scaledComplexClockPairing_error_le Q hZ.2 (hc F) (hc G) (hi F) (hi G)
    (mul_nonneg (Nat.cast_nonneg _) (clockSchwartz_norm_nonneg N G)) hg ht hR
  apply h.trans
  have hV : 0 ≤ clockVarianceConstant d Λ₀ r₀ := by
    unfold clockVarianceConstant
    exact mul_nonneg (sq_nonneg _) (pow_nonneg (by linarith [Q.range_parameter]) _)
  have hb := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hI
      (mul_nonneg (mul_nonneg (zero_le_one.trans Q.range_parameter) hV)
        (mul_nonneg (Nat.cast_nonneg d) (clockSchwartz_norm_nonneg N G))))
    (inv_nonneg.mpr hR.le)
  convert hb using 1
  ring

/-- The clock-clock restriction of covariance scaling. The power and constant
precede the environment; the actual scalar is selected once before all joint
realizations, scales, and tests. This asserts no commutator or cross-block limit. -/
theorem clock_covariance_scaling_component (d : ℕ) (D : StructuralData d)
    (N : ℕ) (hN : 2 * d + 10 < N) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧
    ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
    ∃ q : ℝ, q = clockCovarianceLimit Q ∧ 0 ≤ q ∧ |q| ≤ C ∧
      ∀ Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q),
        IsJointObservation Q Z → ∀ R : ℝ, ∀ hR : 2 ≤ R,
      ∀ F G : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)),
        (∀ x j i, F x (.inl (j, i)) = 0) →
        (∀ x j i, G x (.inl (j, i)) = 0) →
        ‖(∫ ω, scaledJointPairing Q R (by linarith) Z F ω *
          scaledJointPairing Q R (by linarith) Z G ω ∂reducedLaw Q) -
          ∫ x, F x (.inr ()) * (q : ℂ) * G x (.inr ())‖ ≤
          C * schwartzTestNorm N F * schwartzTestNorm N G * R ^ (-ε) := by
  let V := clockVarianceConstant d D.ellipticity D.dependenceRange
  let A := D.dependenceRange * V * d * clockSchwartzWeightMass d N
  have hr : 0 ≤ D.dependenceRange := zero_le_one.trans D.one_le_dependenceRange
  have hV : 0 ≤ V := mul_nonneg (sq_nonneg _) (pow_nonneg (mul_nonneg (by norm_num) hr) _)
  have hW : 0 ≤ clockSchwartzWeightMass d N :=
    integral_nonneg fun _ => Real.rpow_nonneg (by positivity) _
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg (mul_nonneg hr hV) (Nat.cast_nonneg _)) hW
  refine ⟨1, 1 + V + A, by norm_num, by positivity, ?_⟩
  intro Q
  refine ⟨clockCovarianceLimit Q, rfl, clockCovarianceLimit_nonneg Q,
    (abs_clockCovarianceLimit_le Q).trans (by dsimp only [V]; linarith), ?_⟩
  intro Z hZ R hR F G hF hG
  have h := scaledJointPairing_clock_error_le Q (by omega : d < N) Z hZ
    (by linarith : 0 < R) F G hF hG
  rw [show R ^ (-(1 : ℝ)) = R⁻¹ by rw [Real.rpow_neg_one]]
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (show A ≤ 1 + V + A by linarith)
        (clockSchwartz_norm_nonneg N F)) (clockSchwartz_norm_nonneg N G))
    (inv_nonneg.mpr (by linarith)))

/-- The clock block embedded in the literal joint index set. Its zero
commutator entries are bookkeeping for the restricted tests, not assertions
about the unproved commutator or cross covariance. -/
noncomputable def clockCovarianceTensor (Q : EnvironmentLaw d Λ₀ r₀) :
    Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ :=
  Matrix.diagonal (Pi.single (.inr ()) (clockCovarianceLimit Q))

/-- Positivity of the embedded clock block comes from actual variances. -/
theorem clockCovarianceTensor_posSemidef (Q : EnvironmentLaw d Λ₀ r₀) :
    (clockCovarianceTensor Q).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro a
  classical
  by_cases ha : a = .inr ()
  · subst a
    simpa only [Pi.single_eq_same] using! clockCovarianceLimit_nonneg Q
  · simp only [Pi.single_eq_of_ne ha, Pi.zero_apply, le_refl]

/-- The embedded tensor acts by the scalar covariance on the clock coordinate. -/
theorem clockCovarianceTensor_mulVec (Q : EnvironmentLaw d Λ₀ r₀)
    (ξ : JointObservationIndex d → ℝ) :
    (clockCovarianceTensor Q).mulVec ξ =
      Pi.single (.inr ()) (clockCovarianceLimit Q * ξ (.inr ())) := by
  classical
  ext a
  by_cases ha : a = .inr ()
  · subst a
    simp [clockCovarianceTensor, Matrix.mulVec_diagonal]
  · simp [clockCovarianceTensor, Matrix.mulVec_diagonal, Pi.single_eq_of_ne ha]

/-- Exact Euclidean operator bound on the embedded scalar block. -/
theorem clockCovarianceTensor_norm_mulVec_le (Q : EnvironmentLaw d Λ₀ r₀)
    (ξ : EuclideanSpace ℝ (JointObservationIndex d)) :
    ‖WithLp.toLp 2 ((clockCovarianceTensor Q).mulVec (WithLp.ofLp ξ))‖ ≤
      |clockCovarianceLimit Q| * ‖ξ‖ := by
  rw [clockCovarianceTensor_mulVec, PiLp.norm_toLp_single, norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le ξ _) (abs_nonneg _)

/-- The literal joint tensor contraction reduces to its clock term. -/
theorem clockCovarianceTensor_bilinear (Q : EnvironmentLaw d Λ₀ r₀)
    (F G : EuclideanSpace ℂ (JointObservationIndex d)) :
    (∑ a : JointObservationIndex d, ∑ b : JointObservationIndex d,
      F a * (clockCovarianceTensor Q a b : ℂ) * G b) =
      F (.inr ()) * (clockCovarianceLimit Q : ℂ) * G (.inr ()) := by
  classical
  simp [clockCovarianceTensor, Matrix.diagonal, Pi.single_apply, Fintype.sum_sum_type]

/-- Exact clock-only restriction of the frozen joint covariance statement,
including its tensor carrier, Euclidean operator bound and bilinear contraction.
Smoothness and d≥2 are unnecessary for this finite-range clock component. -/
theorem clock_covariance_scaling_restriction (d : ℕ) (D : StructuralData d)
    (N : ℕ) (hN : 2 * d + 10 < N) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧
    ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
    ∃ covariance : Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ,
      covariance = clockCovarianceTensor Q ∧ covariance.PosSemidef ∧
      (∀ ξ : EuclideanSpace ℝ (JointObservationIndex d),
        ‖WithLp.toLp 2 (covariance.mulVec (WithLp.ofLp ξ))‖ ≤ C * ‖ξ‖) ∧
      ∀ Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q),
        IsJointObservation Q Z → ∀ R : ℝ, ∀ hR : 2 ≤ R,
      ∀ F G : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)),
        (∀ x j i, F x (.inl (j, i)) = 0) →
        (∀ x j i, G x (.inl (j, i)) = 0) →
        ‖(∫ ω, scaledJointPairing Q R (by linarith) Z F ω *
          scaledJointPairing Q R (by linarith) Z G ω ∂reducedLaw Q) -
          ∫ x : Vec d, ∑ a : JointObservationIndex d, ∑ b : JointObservationIndex d,
            F x a * (covariance a b : ℂ) * G x b‖ ≤
          C * schwartzTestNorm N F * schwartzTestNorm N G * R ^ (-ε) := by
  obtain ⟨ε, C, hε, hC, h⟩ := clock_covariance_scaling_component d D N hN
  refine ⟨ε, C, hε, hC, fun Q => ?_⟩
  obtain ⟨q, hq, _, hqb, he⟩ := h Q
  subst q
  refine ⟨clockCovarianceTensor Q, rfl, clockCovarianceTensor_posSemidef Q, ?_, ?_⟩
  · intro ξ
    exact (clockCovarianceTensor_norm_mulVec_le Q ξ).trans
      (mul_le_mul_of_nonneg_right hqb (norm_nonneg _))
  · intro Z hZ R hR F G hF hG
    simp_rw [clockCovarianceTensor_bilinear]
    exact he Z hZ R hR F G hF hG

end EinsteinFull
