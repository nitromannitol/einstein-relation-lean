import EinsteinFull.Homogenization.HeatHessianCauchy
import EinsteinFull.Homogenization.GaussianWeightedEnergy

/-!
# The heat formula for functions with Gaussian moments

The heat formula (6.7) of Armstrong, Kuusi and Mourrat, *Quantitative Stochastic Homogenization
and Large-Scale Regularity*, is applied to fluxes that are only locally square integrable, with
square integrals over the balls `B_R` growing at most like `R^d`. Such a function has *Gaussian
moments*: every heat smoothing of `|f|` exists and is bounded on balls. Under this condition the
Hessian convolutions `∂ⱼ∂ᵢΦ_t * f` exist, are bounded on balls uniformly on time windows, and the
time-truncated heat Hessians are square integrable on balls, linear in `f` and additive in the
time window.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace EinsteinFull.Homogenization

open EinsteinRelation EinsteinRelation.Correctors EinsteinRelation.External.AKM

variable {d : ℕ}

/-- **Gaussian moments**: every heat smoothing of `|f|` exists and is bounded on balls. -/
def HasGaussianMoments (f : Vec d → ℝ) : Prop :=
  ∀ s : ℝ, 0 < s → ∀ ρ : ℝ, ∃ B : ℝ, ∀ x : Vec d, euclideanNorm x ≤ ρ →
    Integrable (fun y => euclideanHeatKernel s (x - y) * |f y|) volume ∧
    ∫ y, euclideanHeatKernel s (x - y) * |f y| ≤ B

theorem abs_apply_le_euclideanNorm (x : Vec d) (i : Fin d) : |x i| ≤ euclideanNorm x := by
  rw [euclideanNorm, ← Real.sqrt_sq_eq_abs]
  refine Real.sqrt_le_sqrt ?_
  have h := Finset.single_le_sum (f := fun l => x l * x l) (fun l _ => mul_self_nonneg (x l))
    (Finset.mem_univ i)
  simpa [euclideanSq, dot, sq] using h

theorem norm_le_euclideanNorm' (x : Vec d) : ‖x‖ ≤ euclideanNorm x :=
  (pi_norm_le_iff_of_nonneg (by unfold euclideanNorm; positivity)).mpr fun i => by
    rw [Real.norm_eq_abs]
    exact abs_apply_le_euclideanNorm x i

theorem volume_ball_zero_lt_top (ρ : ℝ) : volume (ball (0 : Vec d) ρ) < ⊤ := by
  refine lt_of_le_of_lt (measure_mono fun x hx => ?_) (measure_closedBall_lt_top (x := 0) (r := ρ))
  have hx' : euclideanNorm (x - 0) < ρ := hx
  rw [sub_zero] at hx'
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (norm_le_euclideanNorm' x).trans hx'.le

/-- Square-integrable functions have Gaussian moments. -/
theorem hasGaussianMoments_of_memLp {f : Vec d → ℝ} (hfm : Measurable f)
    (hf : MemLp f 2 volume) : HasGaussianMoments f := by
  intro s hs ρ
  have hΦ := memLp_euclideanHeatKernel (d := d) hs
  have hsq : Integrable (fun y => f y ^ 2) volume :=
    (memLp_two_iff_integrable_sq hfm.aestronglyMeasurable).1 hf
  have hΦsq : Integrable (fun z => euclideanHeatKernel s z ^ 2) volume :=
    (memLp_two_iff_integrable_sq (measurable_euclideanHeatKernel s).aestronglyMeasurable).1 hΦ
  refine ⟨(∫ z : Vec d, euclideanHeatKernel s z ^ 2) / 2 + (∫ y : Vec d, f y ^ 2) / 2,
    fun x _ => ?_⟩
  have hint := integrable_kernel_mul hΦ hf.abs x
  refine ⟨hint, ?_⟩
  have hΦx : Integrable (fun y => euclideanHeatKernel s (x - y) ^ 2) volume :=
    hΦsq.comp_sub_left x
  calc ∫ y, euclideanHeatKernel s (x - y) * |f y|
      ≤ ∫ y, (euclideanHeatKernel s (x - y) ^ 2 / 2 + f y ^ 2 / 2) := by
        refine integral_mono hint ((hΦx.div_const 2).add (hsq.div_const 2)) fun y => ?_
        nlinarith [sq_nonneg (euclideanHeatKernel s (x - y) - |f y|), sq_abs (f y)]
    _ = (∫ z, euclideanHeatKernel s z ^ 2) / 2 + (∫ y, f y ^ 2) / 2 := by
        rw [integral_add (hΦx.div_const 2) (hsq.div_const 2), integral_div, integral_div,
          integral_sub_left_eq_self (fun z => euclideanHeatKernel s z ^ 2) (μ := volume) x]

/-- Functions whose square integrals on balls grow at most like the volume have Gaussian
moments. -/
theorem hasGaussianMoments_of_growth {f : Vec d → ℝ} (hfm : Measurable f) {M R₀ : ℝ}
    (hM : 0 ≤ M) (hR₀ : 0 < R₀)
    (hball : ∀ R : ℝ, R₀ ≤ R → ∫⁻ y in ball 0 R, ‖f y‖ₑ ^ 2 ≤ ENNReal.ofReal (M * R ^ d)) :
    HasGaussianMoments f := by
  intro s hs ρ
  set S : ℝ := max s (max (R₀ ^ 2) (ρ ^ 2)) with hS
  have hsS : s ≤ S := le_max_left _ _
  have hS0 : 0 < S := lt_of_lt_of_le hs hsS
  have hR₀S : R₀ ^ 2 ≤ S := (le_max_left _ _).trans (le_max_right _ _)
  set K : ℝ := (4 * Real.pi) ^ (-(d : ℝ) / 2) * (2 ^ d + gaussianShellSum d) * M with hK
  have hK0 : 0 ≤ K := by
    have := gaussianShellSum_nonneg d
    positivity
  set c : ℝ := (S / s) ^ ((d : ℝ) / 2) with hc
  have hc0 : 0 ≤ c := by positivity
  refine ⟨1 / 2 + c * K / 2, fun x hx => ?_⟩
  have hxS : euclideanNorm x ≤ Real.sqrt S := by
    rcases le_or_gt ρ 0 with hρ | hρ
    · exact hx.trans (hρ.trans (Real.sqrt_nonneg _))
    · exact hx.trans (Real.le_sqrt_of_sq_le ((le_max_right _ _).trans (le_max_right _ _)))
  have hmom := lintegral_mul_heatKernel_le (f := fun y => ‖f y‖ₑ ^ 2) (hfm.enorm.pow_const 2) hM
    hR₀ hball hR₀S hxS
  have hmeas : Measurable (fun y => euclideanHeatKernel S (x - y) * f y ^ 2) :=
    ((measurable_euclideanHeatKernel S).comp (measurable_const.sub measurable_id)).mul
      (hfm.pow_const 2)
  have hsqint : Integrable (fun y => euclideanHeatKernel S (x - y) * f y ^ 2) volume := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    refine lt_of_le_of_lt (le_of_eq ?_) (lt_of_le_of_lt hmom ENNReal.ofReal_lt_top)
    refine lintegral_congr fun y => ?_
    rw [enorm_mul, mul_comm, show y - x = -(x - y) by abel, euclideanHeatKernel_neg,
      Real.enorm_eq_ofReal (euclideanHeatKernel_nonneg hS0.le _), ← enorm_pow]
  have hsqle : ∫ y, euclideanHeatKernel S (x - y) * f y ^ 2 ≤ K := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun y =>
      mul_nonneg (euclideanHeatKernel_nonneg hS0.le _) (sq_nonneg _)) hmeas.aestronglyMeasurable]
    refine ENNReal.toReal_le_of_le_ofReal hK0 (le_trans (le_of_eq ?_) hmom)
    refine lintegral_congr fun y => ?_
    rw [ENNReal.ofReal_mul (euclideanHeatKernel_nonneg hS0.le _), mul_comm,
      show y - x = -(x - y) by abel, euclideanHeatKernel_neg, ← Real.enorm_eq_ofReal (sq_nonneg _),
      enorm_pow]
  have hΦx : Integrable (fun y => euclideanHeatKernel s (x - y)) volume :=
    (integrable_euclideanHeatKernel hs).comp_sub_left x
  have hdom : ∀ y, euclideanHeatKernel s (x - y) * |f y| ≤
      euclideanHeatKernel s (x - y) / 2 + c * (euclideanHeatKernel S (x - y) * f y ^ 2) / 2 := by
    intro y
    have h0 := euclideanHeatKernel_nonneg hs.le (x - y)
    have h1 := euclideanHeatKernel_le_mul hs hsS (x - y)
    have h2 : euclideanHeatKernel s (x - y) * |f y| ≤
        euclideanHeatKernel s (x - y) / 2 + euclideanHeatKernel s (x - y) * f y ^ 2 / 2 := by
      nlinarith [sq_nonneg (|f y| - 1), sq_abs (f y)]
    have h3 : euclideanHeatKernel s (x - y) * f y ^ 2 ≤
        c * (euclideanHeatKernel S (x - y) * f y ^ 2) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
    linarith
  have hmaj : Integrable (fun y => euclideanHeatKernel s (x - y) / 2 +
      c * (euclideanHeatKernel S (x - y) * f y ^ 2) / 2) volume :=
    (hΦx.div_const 2).add ((hsqint.const_mul c).div_const 2)
  have hint : Integrable (fun y => euclideanHeatKernel s (x - y) * |f y|) volume :=
    hmaj.mono' (((measurable_euclideanHeatKernel s).comp
      (measurable_const.sub measurable_id)).mul
        (continuous_abs.measurable.comp hfm)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (euclideanHeatKernel_nonneg hs.le _)
          (abs_nonneg _))]
        exact hdom y)
  refine ⟨hint, (integral_mono hint hmaj hdom).trans ?_⟩
  rw [integral_add (hΦx.div_const 2) ((hsqint.const_mul c).div_const 2), integral_div,
    integral_div, integral_const_mul, integral_sub_left_eq_self (euclideanHeatKernel (d := d) s)
      (μ := volume) x, integral_euclideanHeatKernel hs]
  have : c * ∫ y, euclideanHeatKernel S (x - y) * f y ^ 2 ≤ c * K :=
    mul_le_mul_of_nonneg_left hsqle hc0
  linarith

section Moments

variable {f : Vec d → ℝ}

theorem HasGaussianMoments.integrable_heatHessian_mul (hf : HasGaussianMoments f) {t : ℝ}
    (ht : 0 < t) (i j : Fin d) (hfm : Measurable f) (x : Vec d) :
    Integrable (fun y => coordinateDerivative j (coordinateDerivative i
      (euclideanHeatKernel t)) (x - y) * f y) volume := by
  obtain ⟨B, hB⟩ := hf (2 * t) (by positivity) (euclideanNorm x)
  have hint := (hB x le_rfl).1
  refine (hint.const_mul ((2 : ℝ) ^ ((d : ℝ) / 2) * (2 / t))).mono'
    (((measurable_heatHessian ht i j).comp (measurable_const.sub measurable_id)).mul
      hfm).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_mul, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (abs_heatHessian_le ht i j _) (abs_nonneg _)

theorem abs_heatHessianConv_le_of_bound {ε₁ ε₂ t : ℝ}
    (hε₁ : 0 < ε₁) (ht : t ∈ Icc ε₁ ε₂) (i j : Fin d) {x : Vec d} {ρ B : ℝ}
    (hB : ∀ x : Vec d, euclideanNorm x ≤ ρ →
      Integrable (fun y => euclideanHeatKernel (2 * ε₂) (x - y) * |f y|) volume ∧
      ∫ y, euclideanHeatKernel (2 * ε₂) (x - y) * |f y| ≤ B) (hx : euclideanNorm x ≤ ρ) :
    |heatHessianConv t i j f x| ≤ windowHessianConst d ε₁ ε₂ * B := by
  have hint := (hB x hx).1
  calc |heatHessianConv t i j f x|
      ≤ ∫ y, windowHessianConst d ε₁ ε₂ * (euclideanHeatKernel (2 * ε₂) (x - y) * |f y|) := by
        refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun y => abs_nonneg _) (hint.const_mul _)
          (Filter.Eventually.of_forall fun y => ?_))
        simp only
        rw [abs_mul, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (abs_heatHessian_le_window hε₁ ht i j _) (abs_nonneg _)
    _ ≤ windowHessianConst d ε₁ ε₂ * B := by
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left (hB x hx).2
          (windowHessianConst_nonneg hε₁ (ht.1.trans ht.2))

theorem aestronglyMeasurable_heatHessianConv_restrict {ε₁ ε₂ : ℝ} (hε₁ : 0 < ε₁) (i j : Fin d)
    (hfm : Measurable f) (x : Vec d) :
    AEStronglyMeasurable (fun t => heatHessianConv t i j f x) (volume.restrict (Icc ε₁ ε₂)) := by
  have hs : StronglyMeasurable (fun t => ∫ y, heatHessianKernel t i j (x - y) * f y) :=
    (stronglyMeasurable_heatHessianKernelConv i j hfm).comp_measurable
      (measurable_id.prodMk measurable_const)
  refine hs.aestronglyMeasurable.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact (heatHessianConv_eq_kernel (lt_of_lt_of_le hε₁ ht.1) i j f x).symm

theorem isFiniteMeasure_restrict_Icc (a b : ℝ) : IsFiniteMeasure (volume.restrict (Icc a b)) := by
  rw [isFiniteMeasure_restrict]
  exact (Real.volume_Icc (a := a) (b := b)).symm ▸ ENNReal.ofReal_ne_top

theorem HasGaussianMoments.integrableOn_heatHessianConv (hf : HasGaussianMoments f)
    {ε₁ ε₂ : ℝ} (hε₁ : 0 < ε₁) (i j : Fin d) (hfm : Measurable f) (x : Vec d) :
    IntegrableOn (fun t => heatHessianConv t i j f x) (Icc ε₁ ε₂) volume := by
  have := isFiniteMeasure_restrict_Icc ε₁ ε₂
  rcases le_or_gt ε₁ ε₂ with hε | hε
  · have hε₂ : 0 < 2 * ε₂ := by linarith
    obtain ⟨B, hB⟩ := hf (2 * ε₂) hε₂ (euclideanNorm x)
    refine (integrable_const (windowHessianConst d ε₁ ε₂ * B)).mono'
      (aestronglyMeasurable_heatHessianConv_restrict hε₁ i j hfm x) ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [Real.norm_eq_abs]
    exact abs_heatHessianConv_le_of_bound hε₁ ht i j hB le_rfl
  · rw [Icc_eq_empty (not_le.mpr hε)]
    exact integrableOn_empty

/-- A bound for the time-truncated heat Hessian on balls. -/
theorem HasGaussianMoments.abs_heatHessianWindow_le (hf : HasGaussianMoments f) {ε₁ ε₂ : ℝ}
    (hε₁ : 0 < ε₁) (hε : ε₁ ≤ ε₂) (i j : Fin d) (ρ : ℝ) :
    ∃ C : ℝ, ∀ x : Vec d, euclideanNorm x ≤ ρ → |heatHessianWindow ε₁ ε₂ i j f x| ≤ C := by
  obtain ⟨B, hB⟩ := hf (2 * ε₂) (by linarith) ρ
  refine ⟨windowHessianConst d ε₁ ε₂ * B * (ε₂ - ε₁), fun x hx => ?_⟩
  have hb := norm_setIntegral_le_of_norm_le_const (s := Icc ε₁ ε₂)
    (f := fun t => heatHessianConv t i j f x)
    (C := windowHessianConst d ε₁ ε₂ * B) (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)
    (fun t ht => by
      rw [Real.norm_eq_abs]
      exact abs_heatHessianConv_le_of_bound hε₁ ht i j hB hx)
  simp only [measureReal_def, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ ε₂ - ε₁)] at hb
  rw [← Real.norm_eq_abs]
  exact hb

/-- The time-truncated heat Hessian is square integrable on balls. -/
theorem HasGaussianMoments.memLp_heatHessianWindow (hf : HasGaussianMoments f) {ε₁ ε₂ : ℝ}
    (hε₁ : 0 < ε₁) (hε : ε₁ ≤ ε₂) (i j : Fin d) (hfm : Measurable f) (ρ : ℝ) :
    MemLp (heatHessianWindow ε₁ ε₂ i j f) 2 (volume.restrict (ball 0 ρ)) := by
  obtain ⟨C, hC⟩ := hf.abs_heatHessianWindow_le hε₁ hε i j ρ
  have hfin : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) ρ)) :=
    isFiniteMeasure_restrict.mpr (volume_ball_zero_lt_top ρ).ne
  refine MemLp.of_bound (stronglyMeasurable_heatHessianWindow hε₁ i j hfm).aestronglyMeasurable C ?_
  filter_upwards [ae_restrict_mem (measurableSet_ball_zero ρ)] with x hx
  rw [Real.norm_eq_abs]
  have hx' : euclideanNorm (x - 0) < ρ := hx
  rw [sub_zero] at hx'
  exact hC x hx'.le

/-- Additivity of the time-truncated heat Hessian over adjacent windows. -/
theorem HasGaussianMoments.heatHessianWindow_add (hf : HasGaussianMoments f) {a b c : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c) (i j : Fin d) (hfm : Measurable f) (x : Vec d) :
    heatHessianWindow a b i j f x + heatHessianWindow b c i j f x =
      heatHessianWindow a c i j f x := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  unfold heatHessianWindow
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab, ← intervalIntegral.integral_of_le hbc,
    ← intervalIntegral.integral_of_le (hab.trans hbc)]
  refine intervalIntegral.integral_add_adjacent_intervals ?_ ?_
  · exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      (hf.integrableOn_heatHessianConv ha i j hfm x)
  · exact (intervalIntegrable_iff_integrableOn_Icc_of_le hbc).mpr
      (hf.integrableOn_heatHessianConv hb i j hfm x)

end Moments

/-- Linearity of the time-truncated heat Hessian on functions with Gaussian moments. -/
theorem heatHessianWindow_add_of_moments {f g : Vec d → ℝ} (hf : HasGaussianMoments f)
    (hg : HasGaussianMoments g) (hfm : Measurable f) (hgm : Measurable g) {ε₁ ε₂ : ℝ}
    (hε₁ : 0 < ε₁) (i j : Fin d) (x : Vec d) :
    heatHessianWindow ε₁ ε₂ i j (f + g) x =
      heatHessianWindow ε₁ ε₂ i j f x + heatHessianWindow ε₁ ε₂ i j g x := by
  unfold heatHessianWindow
  rw [← integral_add (hf.integrableOn_heatHessianConv hε₁ i j hfm x)
    (hg.integrableOn_heatHessianConv hε₁ i j hgm x)]
  refine setIntegral_congr_fun measurableSet_Icc fun t ht => ?_
  have ht0 : 0 < t := lt_of_lt_of_le hε₁ ht.1
  unfold heatHessianConv
  rw [← integral_add (hf.integrable_heatHessian_mul ht0 i j hfm x)
    (hg.integrable_heatHessian_mul ht0 i j hgm x)]
  congr 1
  funext y
  simp only [Pi.add_apply]
  ring

end EinsteinFull.Homogenization
