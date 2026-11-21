import EinsteinFull.Homogenization.HeatFormulaLocal

/-!
# The time-truncated heat gradient

The first derivatives of the heat kernel satisfy `|∂ᵢΦ_t(z)| ≤ 2^(d/2) (2/√t) Φ_{2t}(z)`. For a
function `f` with Gaussian moments, the time-truncated heat gradient
`∫_{ε₁}^{ε₂} ∂ᵢΦ_t * f dt` is therefore defined, bounded on balls and square integrable there. Its
weak gradient is the time-truncated heat Hessian; it is the potential of the truncations of the
heat formula (6.7) in Armstrong, Kuusi and Mourrat, *Quantitative Stochastic Homogenization and
Large-Scale Regularity*.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace EinsteinFull.Homogenization

open EinsteinRelation EinsteinRelation.Correctors EinsteinRelation.External.AKM

variable {d : ℕ}

/-- The explicit first derivative of the heat kernel, jointly in time and space. -/
noncomputable def heatGradKernel (t : ℝ) (i : Fin d) (z : Vec d) : ℝ :=
  euclideanHeatKernel t z * (-(1 / (2 * t)) * z i)

theorem heatGrad_eq (t : ℝ) (i : Fin d) :
    coordinateDerivative i (euclideanHeatKernel (d := d) t) = heatGradKernel t i := by
  funext z
  unfold coordinateDerivative heatGradKernel
  rw [fderiv_euclideanHeatKernel]
  congr 2
  simp [unitVector, Pi.single_apply]

theorem measurable_heatGradKernel (i : Fin d) :
    Measurable (fun p : ℝ × Vec d => heatGradKernel p.1 i p.2) := by
  unfold heatGradKernel
  exact (measurable_euclideanHeatKernel_joint (d := d)).mul (by fun_prop)

theorem measurable_heatGrad (t : ℝ) (i : Fin d) :
    Measurable (coordinateDerivative i (euclideanHeatKernel (d := d) t)) := by
  rw [heatGrad_eq]
  exact (measurable_heatGradKernel i).comp (measurable_const.prodMk measurable_id)

theorem le_exp_sq (w : ℝ) : w ≤ Real.exp (w ^ 2) := by
  have h := Real.add_one_le_exp (w ^ 2)
  nlinarith [sq_nonneg (w - 1)]

/-- **Gaussian bound for the heat-kernel gradient.** -/
theorem abs_heatGrad_le {t : ℝ} (ht : 0 < t) (i : Fin d) (z : Vec d) :
    |coordinateDerivative i (euclideanHeatKernel t) z| ≤
      (2 : ℝ) ^ ((d : ℝ) / 2) * (2 / Real.sqrt t) * euclideanHeatKernel (2 * t) z := by
  rw [heatGrad_eq, heatGradKernel, euclideanHeatKernel_eq_two_mul ht z]
  set s := Real.sqrt t with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr ht
  have hst : s ^ 2 = t := Real.sq_sqrt ht.le
  set N := euclideanNorm z with hN
  have hN0 : 0 ≤ N := by rw [hN]; unfold euclideanNorm; positivity
  have hsq : euclideanSq z = N ^ 2 := euclideanSq_eq_euclideanNorm_sq z
  have hzi : |z i| ≤ N := abs_apply_le_euclideanNorm z i
  set w := N / (4 * s) with hw
  have hw0 : 0 ≤ w := by positivity
  have hNw : N = 4 * s * w := by rw [hw]; field_simp
  have hexp : Real.exp (-euclideanSq z / (8 * t)) ≤ Real.exp (-(w ^ 2)) := by
    apply Real.exp_le_exp.mpr
    rw [hsq, hNw, ← hst]
    have : -(4 * s * w) ^ 2 / (8 * s ^ 2) = -(2 * w ^ 2) := by field_simp; ring
    rw [this]
    nlinarith [sq_nonneg w]
  have hkey : N * Real.exp (-euclideanSq z / (8 * t)) ≤ 4 * s := by
    calc N * Real.exp (-euclideanSq z / (8 * t)) ≤ N * Real.exp (-(w ^ 2)) :=
          mul_le_mul_of_nonneg_left hexp hN0
      _ = 4 * s * (w * Real.exp (-(w ^ 2))) := by rw [hNw]; ring
      _ ≤ 4 * s * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
          exact le_exp_sq w
      _ = 4 * s := mul_one _
  have hK := euclideanHeatKernel_nonneg (d := d) (t := 2 * t) (by positivity) z
  have hE := Real.exp_pos (-euclideanSq z / (8 * t))
  rw [abs_mul, abs_of_nonneg (by positivity), abs_mul, abs_neg,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * t))]
  calc (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-euclideanSq z / (8 * t)) *
        euclideanHeatKernel (2 * t) z * (1 / (2 * t) * |z i|)
      ≤ (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-euclideanSq z / (8 * t)) *
        euclideanHeatKernel (2 * t) z * (1 / (2 * t) * N) := by gcongr
    _ = (2 : ℝ) ^ ((d : ℝ) / 2) * euclideanHeatKernel (2 * t) z *
        (N * Real.exp (-euclideanSq z / (8 * t))) / (2 * t) := by ring
    _ ≤ (2 : ℝ) ^ ((d : ℝ) / 2) * euclideanHeatKernel (2 * t) z * (4 * s) / (2 * t) := by
        gcongr
    _ = (2 : ℝ) ^ ((d : ℝ) / 2) * (2 / s) * euclideanHeatKernel (2 * t) z := by
        rw [← hst]
        field_simp
        ring

/-- The constant dominating the heat-kernel gradient on a time window. -/
noncomputable def windowGradConst (d : ℕ) (ε₁ ε₂ : ℝ) : ℝ :=
  (2 : ℝ) ^ ((d : ℝ) / 2) * (2 / Real.sqrt ε₁) * (ε₂ / ε₁) ^ ((d : ℝ) / 2)

theorem windowGradConst_nonneg {ε₁ : ℝ} (hε₁ : 0 < ε₁) {ε₂ : ℝ} (hε : ε₁ ≤ ε₂) :
    0 ≤ windowGradConst d ε₁ ε₂ := by
  have : 0 < ε₂ := lt_of_lt_of_le hε₁ hε
  unfold windowGradConst
  positivity

theorem abs_heatGrad_le_window {ε₁ ε₂ t : ℝ} (hε₁ : 0 < ε₁) (ht : t ∈ Icc ε₁ ε₂) (i : Fin d)
    (z : Vec d) :
    |coordinateDerivative i (euclideanHeatKernel t) z| ≤
      windowGradConst d ε₁ ε₂ * euclideanHeatKernel (2 * ε₂) z := by
  have ht0 : 0 < t := lt_of_lt_of_le hε₁ ht.1
  have h1 := abs_heatGrad_le ht0 i z
  have h2 := euclideanHeatKernel_le_mul (d := d) (s := 2 * t) (S := 2 * ε₂) (by positivity)
    (by linarith [ht.2]) z
  have h3 : (2 * ε₂ / (2 * t)) ^ ((d : ℝ) / 2) ≤ (ε₂ / ε₁) ^ ((d : ℝ) / 2) := by
    rw [mul_div_mul_left _ _ two_ne_zero]
    exact Real.rpow_le_rpow (div_nonneg (by linarith [ht.1, ht.2]) ht0.le)
      (div_le_div_of_nonneg_left (by linarith [ht.2, ht.1]) hε₁ ht.1) (by positivity)
  have h4 : 2 / Real.sqrt t ≤ 2 / Real.sqrt ε₁ :=
    div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.mpr hε₁) (Real.sqrt_le_sqrt ht.1)
  have hK := euclideanHeatKernel_nonneg (d := d) (t := 2 * ε₂) (by linarith [ht.2]) z
  calc _ ≤ (2 : ℝ) ^ ((d : ℝ) / 2) * (2 / Real.sqrt t) * euclideanHeatKernel (2 * t) z := h1
    _ ≤ (2 : ℝ) ^ ((d : ℝ) / 2) * (2 / Real.sqrt t) *
        ((2 * ε₂ / (2 * t)) ^ ((d : ℝ) / 2) * euclideanHeatKernel (2 * ε₂) z) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ (2 : ℝ) ^ ((d : ℝ) / 2) * (2 / Real.sqrt ε₁) *
        ((ε₂ / ε₁) ^ ((d : ℝ) / 2) * euclideanHeatKernel (2 * ε₂) z) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h4 (by positivity))
          (mul_le_mul_of_nonneg_right h3 hK)
          (mul_nonneg (Real.rpow_nonneg (div_nonneg (by linarith [ht.1, ht.2]) (by linarith)) _)
            hK)
          (by positivity)
    _ = windowGradConst d ε₁ ε₂ * euclideanHeatKernel (2 * ε₂) z := by
        unfold windowGradConst
        ring

/-- Convolution with the heat-kernel gradient `∂ᵢΦ_t`. -/
noncomputable def heatGradConv (t : ℝ) (i : Fin d) (f : Vec d → ℝ) (x : Vec d) : ℝ :=
  ∫ y, coordinateDerivative i (euclideanHeatKernel t) (x - y) * f y

/-- The time-truncated heat gradient `∫_{ε₁}^{ε₂} ∂ᵢΦ_t * f dt`. -/
noncomputable def heatGradWindow (ε₁ ε₂ : ℝ) (i : Fin d) (f : Vec d → ℝ) (x : Vec d) : ℝ :=
  ∫ t in Icc ε₁ ε₂, heatGradConv t i f x

theorem heatGradConv_eq_kernel (t : ℝ) (i : Fin d) (f : Vec d → ℝ) (x : Vec d) :
    heatGradConv t i f x = ∫ y, heatGradKernel t i (x - y) * f y := by
  rw [heatGradConv, heatGrad_eq]

theorem stronglyMeasurable_heatGradKernelConv (i : Fin d) {f : Vec d → ℝ} (hf : Measurable f) :
    StronglyMeasurable (fun p : ℝ × Vec d => ∫ y, heatGradKernel p.1 i (p.2 - y) * f y) :=
  (((measurable_heatGradKernel i).comp ((measurable_fst.comp measurable_fst).prodMk
    ((measurable_snd.comp measurable_fst).sub measurable_snd))).mul
      (hf.comp measurable_snd)).stronglyMeasurable.integral_prod_right'

theorem stronglyMeasurable_heatGradWindow (ε₁ ε₂ : ℝ) (i : Fin d) {f : Vec d → ℝ}
    (hf : Measurable f) : StronglyMeasurable (heatGradWindow ε₁ ε₂ i f) := by
  have h : heatGradWindow ε₁ ε₂ i f = fun x =>
      ∫ t in Icc ε₁ ε₂, ∫ y, heatGradKernel t i (x - y) * f y := by
    funext x
    unfold heatGradWindow
    simp_rw [heatGradConv_eq_kernel]
  rw [h]
  exact (stronglyMeasurable_heatGradKernelConv i hf).integral_prod_left

section Moments

variable {f : Vec d → ℝ}

theorem HasGaussianMoments.integrable_heatGrad_mul (hf : HasGaussianMoments f) {t : ℝ}
    (ht : 0 < t) (i : Fin d) (hfm : Measurable f) (x : Vec d) :
    Integrable (fun y => coordinateDerivative i (euclideanHeatKernel t) (x - y) * f y) volume := by
  obtain ⟨B, hB⟩ := hf (2 * t) (by positivity) (euclideanNorm x)
  refine ((hB x le_rfl).1.const_mul ((2 : ℝ) ^ ((d : ℝ) / 2) * (2 / Real.sqrt t))).mono'
    (((measurable_heatGrad t i).comp (measurable_const.sub measurable_id)).mul
      hfm).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_mul, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (abs_heatGrad_le ht i _) (abs_nonneg _)

theorem abs_heatGradConv_le_of_bound {ε₁ ε₂ t : ℝ} (hε₁ : 0 < ε₁) (ht : t ∈ Icc ε₁ ε₂)
    (i : Fin d) {x : Vec d} {ρ B : ℝ}
    (hB : ∀ x : Vec d, euclideanNorm x ≤ ρ →
      Integrable (fun y => euclideanHeatKernel (2 * ε₂) (x - y) * |f y|) volume ∧
      ∫ y, euclideanHeatKernel (2 * ε₂) (x - y) * |f y| ≤ B) (hx : euclideanNorm x ≤ ρ) :
    |heatGradConv t i f x| ≤ windowGradConst d ε₁ ε₂ * B := by
  have hint := (hB x hx).1
  calc |heatGradConv t i f x|
      ≤ ∫ y, windowGradConst d ε₁ ε₂ * (euclideanHeatKernel (2 * ε₂) (x - y) * |f y|) := by
        refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun y => abs_nonneg _) (hint.const_mul _)
          (Filter.Eventually.of_forall fun y => ?_))
        simp only
        rw [abs_mul, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (abs_heatGrad_le_window hε₁ ht i _) (abs_nonneg _)
    _ ≤ windowGradConst d ε₁ ε₂ * B := by
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left (hB x hx).2
          (windowGradConst_nonneg hε₁ (ht.1.trans ht.2))

theorem aestronglyMeasurable_heatGradConv_restrict (s : Set ℝ) (i : Fin d) (hfm : Measurable f)
    (x : Vec d) :
    AEStronglyMeasurable (fun t => heatGradConv t i f x) (volume.restrict s) := by
  have hs : StronglyMeasurable (fun t => ∫ y, heatGradKernel t i (x - y) * f y) :=
    (stronglyMeasurable_heatGradKernelConv i hfm).comp_measurable
      (measurable_id.prodMk measurable_const)
  exact hs.aestronglyMeasurable.congr (Filter.Eventually.of_forall fun t =>
    (heatGradConv_eq_kernel t i f x).symm)

theorem HasGaussianMoments.integrableOn_heatGradConv (hf : HasGaussianMoments f)
    {ε₁ ε₂ : ℝ} (hε₁ : 0 < ε₁) (i : Fin d) (hfm : Measurable f) (x : Vec d) :
    IntegrableOn (fun t => heatGradConv t i f x) (Icc ε₁ ε₂) volume := by
  have := isFiniteMeasure_restrict_Icc ε₁ ε₂
  rcases le_or_gt ε₁ ε₂ with hε | hε
  · obtain ⟨B, hB⟩ := hf (2 * ε₂) (by linarith) (euclideanNorm x)
    refine (integrable_const (windowGradConst d ε₁ ε₂ * B)).mono'
      (aestronglyMeasurable_heatGradConv_restrict _ i hfm x) ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [Real.norm_eq_abs]
    exact abs_heatGradConv_le_of_bound hε₁ ht i hB le_rfl
  · rw [Icc_eq_empty (not_le.mpr hε)]
    exact integrableOn_empty

theorem HasGaussianMoments.abs_heatGradWindow_le (hf : HasGaussianMoments f) {ε₁ ε₂ : ℝ}
    (hε₁ : 0 < ε₁) (hε : ε₁ ≤ ε₂) (i : Fin d) (ρ : ℝ) :
    ∃ C : ℝ, ∀ x : Vec d, euclideanNorm x ≤ ρ → |heatGradWindow ε₁ ε₂ i f x| ≤ C := by
  obtain ⟨B, hB⟩ := hf (2 * ε₂) (by linarith) ρ
  refine ⟨windowGradConst d ε₁ ε₂ * B * (ε₂ - ε₁), fun x hx => ?_⟩
  have hb := norm_setIntegral_le_of_norm_le_const (s := Icc ε₁ ε₂)
    (f := fun t => heatGradConv t i f x)
    (C := windowGradConst d ε₁ ε₂ * B) (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)
    (fun t ht => by
      rw [Real.norm_eq_abs]
      exact abs_heatGradConv_le_of_bound hε₁ ht i hB hx)
  simp only [measureReal_def, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ ε₂ - ε₁)] at hb
  rw [← Real.norm_eq_abs]
  exact hb

theorem HasGaussianMoments.memLp_heatGradWindow (hf : HasGaussianMoments f) {ε₁ ε₂ : ℝ}
    (hε₁ : 0 < ε₁) (hε : ε₁ ≤ ε₂) (i : Fin d) (hfm : Measurable f) (ρ : ℝ) :
    MemLp (heatGradWindow ε₁ ε₂ i f) 2 (volume.restrict (ball 0 ρ)) := by
  obtain ⟨C, hC⟩ := hf.abs_heatGradWindow_le hε₁ hε i ρ
  have hfin : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) ρ)) :=
    isFiniteMeasure_restrict.mpr (volume_ball_zero_lt_top ρ).ne
  refine MemLp.of_bound (stronglyMeasurable_heatGradWindow ε₁ ε₂ i hfm).aestronglyMeasurable C ?_
  filter_upwards [ae_restrict_mem (measurableSet_ball_zero ρ)] with x hx
  have hx' : euclideanNorm (x - 0) < ρ := hx
  rw [sub_zero] at hx'
  rw [Real.norm_eq_abs]
  exact hC x hx'.le

end Moments

end EinsteinFull.Homogenization
