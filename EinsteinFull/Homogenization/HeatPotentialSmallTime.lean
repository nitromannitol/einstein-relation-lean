import EinsteinFull.Homogenization.HeatPotentialOscillation
import EinsteinFull.Homogenization.GaussianWeightedEnergy

/-!
# The small-time part of the truncated heat potential

The heat-kernel gradient has integral zero, so the time-truncated heat gradient
`∫_ε^T ∂ᵢΦ_t * F dt` does not see constants; it is additive over adjacent time windows.

Let `F` satisfy `∫_{B_R} F² ≤ M R^d` for `R ≥ R₀`. For `r ≥ R₀` and `0 < ε ≤ T ≤ r²` the
truncated heat gradient `W = ∫_ε^T ∂ᵢΦ_t * F dt` satisfies `∫_{B_r} W² ≤ C M T r^d`, with `C`
depending only on `d`. The proof bounds `|∂ᵢΦ_t * F| ≤ c t^(-1/2) Φ_{2t} * |F|`, applies the
weighted Cauchy–Schwarz inequality in time with the weight `t^(-1/2)` and in space with the
weight `Φ_{2t}`, and localizes the heat kernel: for `|x| ≤ r` and `t ≤ r²`,
`Φ_{2t}(x - y) ≤ 2^(d/2) e^(1/16) e^(-|y|²/(32 r²)) Φ_{4t}(x - y)`, so that the energy bound
enters through the Gaussian-weighted energy at the scale `8 r²`. This is the small-time part of
the proof of the flux corrector estimate (6.13) of Armstrong, Kuusi and Mourrat, *Quantitative
Stochastic Homogenization and Large-Scale Regularity*.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace EinsteinFull.Homogenization

open EinsteinRelation EinsteinRelation.Correctors EinsteinRelation.External.AKM

variable {d : ℕ}

section Constants

/-- The heat-kernel gradient has integral zero. -/
theorem integral_heatGrad_eq_zero {t : ℝ} (ht : 0 < t) (i : Fin d) :
    ∫ z, coordinateDerivative i (euclideanHeatKernel (d := d) t) z = 0 := by
  have hΦ := (contDiff_euclideanHeatKernel (d := d) t).differentiable (by simp)
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun _ : Vec d => (1 : ℝ)) (g := euclideanHeatKernel t)
    (v := unitVector i) (by simp) (by simp only [one_mul]; exact integrable_heatGrad ht i)
    (by simp only [one_mul]; exact integrable_euclideanHeatKernel ht)
    (fun x _ => differentiableAt_const _) (fun x _ => hΦ x)
  simpa [coordinateDerivative] using h

/-- The heat-kernel gradient does not see constants. -/
theorem heatGradConv_add_const {t : ℝ} (ht : 0 < t) (i : Fin d) {f : Vec d → ℝ} (x : Vec d)
    (hf : Integrable (fun y => coordinateDerivative i (euclideanHeatKernel t) (x - y) * f y)
      volume) (c : ℝ) :
    heatGradConv t i (fun y => f y + c) x = heatGradConv t i f x := by
  unfold heatGradConv
  have hK := (integrable_heatGrad (d := d) ht i).comp_sub_left x
  simp_rw [mul_add]
  rw [integral_add hf (hK.mul_const c), integral_mul_const,
    integral_sub_left_eq_self (fun z => coordinateDerivative i (euclideanHeatKernel (d := d) t) z)
      (μ := volume) x, integral_heatGrad_eq_zero ht, zero_mul, add_zero]

variable {f : Vec d → ℝ}

/-- The time-truncated heat gradient does not see constants. -/
theorem HasGaussianMoments.heatGradWindow_add_const (hf : HasGaussianMoments f)
    (hfm : Measurable f) {ε₁ ε₂ : ℝ} (hε₁ : 0 < ε₁) (i : Fin d) (c : ℝ) (x : Vec d) :
    heatGradWindow ε₁ ε₂ i (fun y => f y + c) x = heatGradWindow ε₁ ε₂ i f x := by
  unfold heatGradWindow
  refine setIntegral_congr_fun measurableSet_Icc fun t ht => ?_
  have ht0 : 0 < t := lt_of_lt_of_le hε₁ ht.1
  exact heatGradConv_add_const ht0 i x (hf.integrable_heatGrad_mul ht0 i hfm x) c

/-- Additivity of the time-truncated heat gradient over adjacent windows. -/
theorem HasGaussianMoments.heatGradWindow_add (hf : HasGaussianMoments f) (hfm : Measurable f)
    {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c) (i : Fin d) (x : Vec d) :
    heatGradWindow a b i f x + heatGradWindow b c i f x = heatGradWindow a c i f x := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  unfold heatGradWindow
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab, ← intervalIntegral.integral_of_le hbc,
    ← intervalIntegral.integral_of_le (hab.trans hbc)]
  exact intervalIntegral.integral_add_adjacent_intervals
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      (hf.integrableOn_heatGradConv ha i hfm x))
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hbc).mpr
      (hf.integrableOn_heatGradConv hb i hfm x))

end Constants

section Localization

theorem euclideanSq_le_two_mul_add (x y : Vec d) :
    euclideanSq y ≤ 2 * euclideanSq (x - y) + 2 * euclideanSq x := by
  unfold euclideanSq dot
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun l _ => ?_
  simp only [Pi.sub_apply]
  nlinarith [sq_nonneg (2 * x l - y l)]

/-- **Localization of the heat kernel** at times `t ≤ r²` and points `|x| ≤ r`. -/
theorem euclideanHeatKernel_two_mul_le {r t : ℝ} (hr : 0 < r) (ht : 0 < t) (htr : t ≤ r ^ 2)
    {x : Vec d} (hx : euclideanNorm x ≤ r) (y : Vec d) :
    euclideanHeatKernel (2 * t) (x - y) ≤
      (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (1 / 16) * Real.exp (-euclideanSq y / (32 * r ^ 2)) *
        euclideanHeatKernel (2 * (2 * t)) (x - y) := by
  rw [euclideanHeatKernel_eq_two_mul (by positivity : (0 : ℝ) < 2 * t) (x - y)]
  have hK := euclideanHeatKernel_nonneg (d := d) (t := 2 * (2 * t)) (by positivity) (x - y)
  have hu : 0 ≤ euclideanSq (x - y) := by
    rw [euclideanSq_eq_euclideanNorm_sq]
    positivity
  have hx2 : euclideanSq x ≤ r ^ 2 := by
    rw [euclideanSq_eq_euclideanNorm_sq]
    exact pow_le_pow_left₀ (euclideanNorm_nonneg x) hx 2
  have hy := euclideanSq_le_two_mul_add x y
  have hexp : Real.exp (-euclideanSq (x - y) / (8 * (2 * t))) ≤
      Real.exp (1 / 16) * Real.exp (-euclideanSq y / (32 * r ^ 2)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hr2 : 0 < r ^ 2 := by positivity
    have h1 : euclideanSq (x - y) / (16 * r ^ 2) ≤ euclideanSq (x - y) / (16 * t) :=
      div_le_div_of_nonneg_left hu (by positivity) (by linarith)
    have h2 : (euclideanSq y - 2 * r ^ 2) / (32 * r ^ 2) ≤
        2 * euclideanSq (x - y) / (32 * r ^ 2) :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    have h2' : (euclideanSq y - 2 * r ^ 2) / (32 * r ^ 2) =
        euclideanSq y / (32 * r ^ 2) - 1 / 16 := by
      rw [sub_div, show 2 * r ^ 2 / (32 * r ^ 2) = 1 / 16 by
        rw [div_eq_div_iff (by positivity) (by norm_num)]
        ring]
    have e2 : 2 * euclideanSq (x - y) / (32 * r ^ 2) = euclideanSq (x - y) / (16 * r ^ 2) := by
      rw [div_eq_div_iff (by positivity) (by positivity)]
      ring
    have e1 : -euclideanSq (x - y) / (8 * (2 * t)) = -(euclideanSq (x - y) / (16 * t)) := by
      rw [neg_div]
      congr 2
      ring
    have e4 : -euclideanSq y / (32 * r ^ 2) = -(euclideanSq y / (32 * r ^ 2)) := neg_div _ _
    rw [h2', e2] at h2
    rw [e1, e4]
    linarith
  calc (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-euclideanSq (x - y) / (8 * (2 * t))) *
        euclideanHeatKernel (2 * (2 * t)) (x - y)
      ≤ (2 : ℝ) ^ ((d : ℝ) / 2) * (Real.exp (1 / 16) * Real.exp (-euclideanSq y / (32 * r ^ 2))) *
        euclideanHeatKernel (2 * (2 * t)) (x - y) := by gcongr
    _ = _ := by ring

theorem lintegral_ofReal_euclideanHeatKernel {t : ℝ} (ht : 0 < t) :
    ∫⁻ z : Vec d, ENNReal.ofReal (euclideanHeatKernel t z) = 1 := by
  rw [← lintegral_enorm_euclideanHeatKernel ht]
  refine lintegral_congr fun z => ?_
  rw [Real.enorm_eq_ofReal (euclideanHeatKernel_nonneg ht.le z)]

/-- The mass of `Φ_{2t}(· - y)` on `B_r` decays like `e^(-|y|²/(32 r²))` for `t ≤ r²`. -/
theorem lintegral_ball_euclideanHeatKernel_le {r t : ℝ} (hr : 0 < r) (ht : 0 < t)
    (htr : t ≤ r ^ 2) (y : Vec d) :
    ∫⁻ x in ball 0 r, ENNReal.ofReal (euclideanHeatKernel (2 * t) (x - y)) ≤
      ENNReal.ofReal ((2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (1 / 16) *
        Real.exp (-euclideanSq y / (32 * r ^ 2))) := by
  set c := (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (1 / 16) *
    Real.exp (-euclideanSq y / (32 * r ^ 2)) with hcdef
  have hc : 0 ≤ c := by positivity
  calc ∫⁻ x in ball 0 r, ENNReal.ofReal (euclideanHeatKernel (2 * t) (x - y))
      ≤ ∫⁻ x in ball 0 r, ENNReal.ofReal c *
          ENNReal.ofReal (euclideanHeatKernel (2 * (2 * t)) (x - y)) := by
        refine setLIntegral_mono' (measurableSet_ball_zero r) fun x hx => ?_
        rw [← ENNReal.ofReal_mul hc]
        refine ENNReal.ofReal_le_ofReal (euclideanHeatKernel_two_mul_le hr ht htr ?_ y)
        have hx' : euclideanNorm (x - 0) < r := hx
        rw [sub_zero] at hx'
        exact hx'.le
    _ ≤ ∫⁻ x, ENNReal.ofReal c * ENNReal.ofReal (euclideanHeatKernel (2 * (2 * t)) (x - y)) :=
        setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal c := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_sub_right_eq_self
            (fun z => ENNReal.ofReal (euclideanHeatKernel (2 * (2 * t)) z)) y,
          lintegral_ofReal_euclideanHeatKernel (by positivity), mul_one]

theorem exp_neg_div_eq_mul_euclideanHeatKernel {s : ℝ} (hs : 0 < s) (y : Vec d) :
    Real.exp (-euclideanSq y / (4 * s)) =
      (4 * Real.pi * s) ^ ((d : ℝ) / 2) * euclideanHeatKernel s y := by
  unfold euclideanHeatKernel
  rw [← mul_assoc, ← Real.rpow_add (by positivity), show (d : ℝ) / 2 + -(d : ℝ) / 2 = 0 by ring,
    Real.rpow_zero, one_mul]

theorem sq_rpow_half_eq {r : ℝ} (hr : 0 ≤ r) : (r ^ 2) ^ ((d : ℝ) / 2) = r ^ d := by
  rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr, ← Real.rpow_natCast r d]
  congr 1
  push_cast
  ring

/-- The Gaussian constant of the small-time bound. -/
noncomputable def smallTimeGaussConst (d : ℕ) : ℝ :=
  (32 * Real.pi) ^ ((d : ℝ) / 2) * ((4 * Real.pi) ^ (-(d : ℝ) / 2) * (2 ^ d + gaussianShellSum d))

theorem smallTimeGaussConst_nonneg (d : ℕ) : 0 ≤ smallTimeGaussConst d := by
  unfold smallTimeGaussConst
  have := gaussianShellSum_nonneg d
  positivity

/-- **Gaussian-weighted energy at the scale `8 r²`.** -/
theorem lintegral_mul_exp_le {f : Vec d → ℝ≥0∞} (hf : Measurable f) {M R₀ : ℝ} (hM : 0 ≤ M)
    (hR₀ : 0 < R₀)
    (hball : ∀ R : ℝ, R₀ ≤ R → ∫⁻ y in ball 0 R, f y ≤ ENNReal.ofReal (M * R ^ d))
    {r : ℝ} (hr : R₀ ≤ r) :
    ∫⁻ y, f y * ENNReal.ofReal (Real.exp (-euclideanSq y / (32 * r ^ 2))) ≤
      ENNReal.ofReal (smallTimeGaussConst d * M * r ^ d) := by
  have hr0 : 0 < r := lt_of_lt_of_le hR₀ hr
  have hs : (0 : ℝ) < 8 * r ^ 2 := by positivity
  have hR2 : R₀ ^ 2 ≤ 8 * r ^ 2 := by nlinarith
  have h0 : euclideanNorm (0 : Vec d) ≤ Real.sqrt (8 * r ^ 2) := by
    have : euclideanNorm (0 : Vec d) = 0 := by simp [euclideanNorm, euclideanSq, dot]
    rw [this]
    exact Real.sqrt_nonneg _
  have hK := lintegral_mul_heatKernel_le hf hM hR₀ hball hR2 h0
  have hc : 0 ≤ (4 * Real.pi * (8 * r ^ 2)) ^ ((d : ℝ) / 2) := by positivity
  have heq : ∀ y : Vec d, Real.exp (-euclideanSq y / (32 * r ^ 2)) =
      (4 * Real.pi * (8 * r ^ 2)) ^ ((d : ℝ) / 2) * euclideanHeatKernel (8 * r ^ 2) (y - 0) := by
    intro y
    rw [sub_zero, ← exp_neg_div_eq_mul_euclideanHeatKernel hs y]
    congr 1
    ring
  have hc' : (4 * Real.pi * (8 * r ^ 2)) ^ ((d : ℝ) / 2) =
      (32 * Real.pi) ^ ((d : ℝ) / 2) * r ^ d := by
    rw [show 4 * Real.pi * (8 * r ^ 2) = 32 * Real.pi * r ^ 2 by ring,
      Real.mul_rpow (by positivity) (by positivity), sq_rpow_half_eq hr0.le]
  calc ∫⁻ y, f y * ENNReal.ofReal (Real.exp (-euclideanSq y / (32 * r ^ 2)))
      = ENNReal.ofReal ((4 * Real.pi * (8 * r ^ 2)) ^ ((d : ℝ) / 2)) *
          ∫⁻ y, f y * ENNReal.ofReal (euclideanHeatKernel (8 * r ^ 2) (y - 0)) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun y => ?_
        rw [heq y, ENNReal.ofReal_mul hc]
        ring
    _ ≤ ENNReal.ofReal ((4 * Real.pi * (8 * r ^ 2)) ^ ((d : ℝ) / 2)) * ENNReal.ofReal
          ((4 * Real.pi) ^ (-(d : ℝ) / 2) * (2 ^ d + gaussianShellSum d) * M) := by gcongr
    _ = ENNReal.ofReal (smallTimeGaussConst d * M * r ^ d) := by
        rw [← ENNReal.ofReal_mul hc, hc']
        unfold smallTimeGaussConst
        congr 1
        ring

end Localization

section SmallTime

/-- The constant of the Gaussian bound for the heat-kernel gradient. -/
noncomputable def smallTimeGradConst (d : ℕ) : ℝ := (2 : ℝ) ^ ((d : ℝ) / 2) * 2

theorem smallTimeGradConst_nonneg (d : ℕ) : 0 ≤ smallTimeGradConst d := by
  unfold smallTimeGradConst
  positivity

/-- The time weight `c t^(-1/2)` of the small-time bound. -/
noncomputable def smallTimeWeight (d : ℕ) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (smallTimeGradConst d * t ^ (-(1 / 2 : ℝ)))

theorem measurable_smallTimeWeight (d : ℕ) : Measurable (smallTimeWeight d) :=
  (measurable_const.mul (measurable_id.pow_const _)).ennreal_ofReal

/-- The heat convolution `∫ Φ_{2t}(x - y) ‖F y‖ₑ ^ n dy`. -/
noncomputable def heatConvEnorm (F : Vec d → ℝ) (n : ℕ) (t : ℝ) (x : Vec d) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (euclideanHeatKernel (2 * t) (x - y)) * ‖F y‖ₑ ^ n

/-- The heat-kernel gradient convolution is dominated by the heat convolution of `|F|`. -/
theorem enorm_heatGradConv_le {t : ℝ} (ht : 0 < t) (i : Fin d) (F : Vec d → ℝ) (x : Vec d) :
    ‖heatGradConv t i F x‖ₑ ≤ smallTimeWeight d t * heatConvEnorm F 1 t x := by
  unfold smallTimeWeight heatConvEnorm smallTimeGradConst
  simp only [pow_one]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun y => ?_)
  rw [enorm_mul, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  gcongr
  rw [Real.enorm_eq_ofReal_abs]
  refine ENNReal.ofReal_le_ofReal ((abs_heatGrad_le ht i (x - y)).trans_eq ?_)
  rw [Real.rpow_neg ht.le, ← Real.sqrt_eq_rpow]
  ring

theorem measurable_heatConvEnorm {F : Vec d → ℝ} (hFm : Measurable F) (n : ℕ) :
    Measurable (fun p : ℝ × Vec d => heatConvEnorm F n p.1 p.2) := by
  unfold heatConvEnorm
  refine Measurable.lintegral_prod_right' (f := fun (p : (ℝ × Vec d) × Vec d) =>
    ENNReal.ofReal (euclideanHeatKernel (2 * p.1.1) (p.1.2 - p.2)) * ‖F p.2‖ₑ ^ n) ?_
  refine Measurable.mul ?_ ((hFm.enorm.comp measurable_snd).pow_const n)
  exact (measurable_euclideanHeatKernel_joint.comp ((measurable_const.mul
    (measurable_fst.comp measurable_fst)).prodMk
      ((measurable_snd.comp measurable_fst).sub measurable_snd))).ennreal_ofReal

theorem measurable_heatConvEnorm_time {F : Vec d → ℝ} (hFm : Measurable F) (n : ℕ)
    (x : Vec d) : Measurable (fun t => heatConvEnorm F n t x) := by
  unfold heatConvEnorm
  refine Measurable.lintegral_prod_right' (f := fun (p : ℝ × Vec d) =>
    ENNReal.ofReal (euclideanHeatKernel (2 * p.1) (x - p.2)) * ‖F p.2‖ₑ ^ n) ?_
  refine Measurable.mul ?_ ((hFm.enorm.comp measurable_snd).pow_const n)
  exact (measurable_euclideanHeatKernel_joint.comp ((measurable_const.mul
    measurable_fst).prodMk (measurable_const.sub measurable_snd))).ennreal_ofReal

theorem measurable_heatConvEnorm_swap {F : Vec d → ℝ} (hFm : Measurable F) (n : ℕ) :
    Measurable (fun p : Vec d × ℝ => heatConvEnorm F n p.2 p.1) := by
  unfold heatConvEnorm
  refine Measurable.lintegral_prod_right' (f := fun (p : (Vec d × ℝ) × Vec d) =>
    ENNReal.ofReal (euclideanHeatKernel (2 * p.1.2) (p.1.1 - p.2)) * ‖F p.2‖ₑ ^ n) ?_
  refine Measurable.mul ?_ ((hFm.enorm.comp measurable_snd).pow_const n)
  exact (measurable_euclideanHeatKernel_joint.comp ((measurable_const.mul
    (measurable_snd.comp measurable_fst)).prodMk
      ((measurable_fst.comp measurable_fst).sub measurable_snd))).ennreal_ofReal

theorem heatConvEnorm_sq_le {t : ℝ} (ht : 0 < t) {F : Vec d → ℝ} (hFm : Measurable F)
    (x : Vec d) : heatConvEnorm F 1 t x ^ 2 ≤ heatConvEnorm F 2 t x := by
  unfold heatConvEnorm
  simp only [pow_one]
  have hw : Measurable fun y => ENNReal.ofReal (euclideanHeatKernel (2 * t) (x - y)) :=
    ((measurable_euclideanHeatKernel (2 * t)).comp
      (measurable_const.sub measurable_id)).ennreal_ofReal
  have h := sq_lintegral_mul_le (μ := volume) hw.aemeasurable hFm.enorm.aemeasurable
  have hmass : ∫⁻ y, ENNReal.ofReal (euclideanHeatKernel (d := d) (2 * t) (x - y)) = 1 := by
    rw [lintegral_sub_left_eq_self (fun z => ENNReal.ofReal (euclideanHeatKernel (2 * t) z)) x,
      lintegral_ofReal_euclideanHeatKernel (by positivity)]
  rwa [hmass, one_mul] at h

/-- For `t ≤ r²`, the heat convolution of `F²` has mass at most `C M r^d` on `B_r`. -/
theorem lintegral_ball_heatConvEnorm_sq_le {F : Vec d → ℝ} (hFm : Measurable F) {M R₀ : ℝ}
    (hM : 0 ≤ M) (hR₀ : 0 < R₀)
    (hgrowth : ∀ R : ℝ, R₀ ≤ R → ∫⁻ y in ball 0 R, ‖F y‖ₑ ^ 2 ≤ ENNReal.ofReal (M * R ^ d))
    {r t : ℝ} (hr : R₀ ≤ r) (ht : 0 < t) (htr : t ≤ r ^ 2) :
    ∫⁻ x in ball 0 r, heatConvEnorm F 2 t x ≤ ENNReal.ofReal ((2 : ℝ) ^ ((d : ℝ) / 2) *
      Real.exp (1 / 16) * (smallTimeGaussConst d * M * r ^ d)) := by
  have hr0 : 0 < r := lt_of_lt_of_le hR₀ hr
  unfold heatConvEnorm
  have hjm : Measurable (Function.uncurry fun (x y : Vec d) =>
      ENNReal.ofReal (euclideanHeatKernel (2 * t) (x - y)) * ‖F y‖ₑ ^ 2) :=
    ((measurable_euclideanHeatKernel (2 * t)).comp
      (measurable_fst.sub measurable_snd)).ennreal_ofReal.mul
      ((hFm.enorm.comp measurable_snd).pow_const 2)
  calc ∫⁻ x in ball 0 r, ∫⁻ y, ENNReal.ofReal (euclideanHeatKernel (2 * t) (x - y)) *
        ‖F y‖ₑ ^ 2
      = ∫⁻ y, ∫⁻ x in ball 0 r,
          ENNReal.ofReal (euclideanHeatKernel (2 * t) (x - y)) * ‖F y‖ₑ ^ 2 :=
        lintegral_lintegral_swap hjm.aemeasurable
    _ = ∫⁻ y, (∫⁻ x in ball 0 r, ENNReal.ofReal (euclideanHeatKernel (2 * t) (x - y))) *
          ‖F y‖ₑ ^ 2 := by
        refine lintegral_congr fun y => ?_
        exact lintegral_mul_const' _ _ (ENNReal.pow_ne_top enorm_ne_top)
    _ ≤ ∫⁻ y, ENNReal.ofReal ((2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (1 / 16) *
          Real.exp (-euclideanSq y / (32 * r ^ 2))) * ‖F y‖ₑ ^ 2 :=
        lintegral_mono fun y =>
          mul_le_mul' (lintegral_ball_euclideanHeatKernel_le hr0 ht htr y) le_rfl
    _ = ENNReal.ofReal ((2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (1 / 16)) *
          ∫⁻ y, ‖F y‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-euclideanSq y / (32 * r ^ 2))) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun y => ?_
        rw [ENNReal.ofReal_mul (by positivity)]
        ring
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (1 / 16)) *
          ENNReal.ofReal (smallTimeGaussConst d * M * r ^ d) := by
        gcongr
        exact lintegral_mul_exp_le (hFm.enorm.pow_const 2) hM hR₀ hgrowth hr
    _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]

theorem lintegral_Icc_rpow_neg_half_le {ε T c : ℝ} (hε : 0 < ε) (hεT : ε ≤ T) (hc : 0 ≤ c) :
    ∫⁻ t in Icc ε T, ENNReal.ofReal (c * t ^ (-(1 / 2 : ℝ))) ≤
      ENNReal.ofReal (c * (2 * T ^ (1 / 2 : ℝ))) := by
  have hint : IntegrableOn (fun t : ℝ => c * t ^ (-(1 / 2 : ℝ))) (Icc ε T) volume := by
    have hco : ContinuousOn (fun t : ℝ => c * t ^ (-(1 / 2 : ℝ))) (Icc ε T) :=
      fun t ht => (continuousAt_const.mul (Real.continuousAt_rpow_const _ _ (Or.inl
        (lt_of_lt_of_le hε ht.1).ne'))).continuousWithinAt
    exact hco.integrableOn_Icc
  rw [← ofReal_integral_eq_lintegral_ofReal hint (by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact mul_nonneg hc (Real.rpow_nonneg (hε.le.trans ht.1) _))]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hεT,
    intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num))]
  have hε' : 0 ≤ ε ^ (-(1 / 2 : ℝ) + 1) := Real.rpow_nonneg hε.le _
  have e : -(1 / 2 : ℝ) + 1 = 1 / 2 := by norm_num
  rw [e] at hε' ⊢
  have hT' : 0 ≤ T ^ (1 / 2 : ℝ) := Real.rpow_nonneg (hε.le.trans hεT) _
  refine mul_le_mul_of_nonneg_left ?_ hc
  rw [div_le_iff₀ (by norm_num)]
  nlinarith

/-- The constant of the small-time bound. -/
noncomputable def smallTimeConst (d : ℕ) : ℝ :=
  4 * smallTimeGradConst d ^ 2 * ((2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (1 / 16) *
    smallTimeGaussConst d)

theorem smallTimeConst_nonneg (d : ℕ) : 0 ≤ smallTimeConst d := by
  unfold smallTimeConst
  have := smallTimeGaussConst_nonneg d
  positivity

/-- **Small-time bound for the truncated heat potential.** If `∫_{B_R} F² ≤ M R^d` for
`R ≥ R₀`, then for `r ≥ R₀` and `0 < ε ≤ T ≤ r²`,
`∫_{B_r} |∫_ε^T ∂ᵢΦ_t * F dt|² ≤ C M T r^d`. -/
theorem lintegral_heatGradWindow_sq_le {F : Vec d → ℝ} (hFm : Measurable F) {M R₀ : ℝ}
    (hM : 0 ≤ M) (hR₀ : 0 < R₀)
    (hgrowth : ∀ R : ℝ, R₀ ≤ R → ∫⁻ y in ball 0 R, ‖F y‖ₑ ^ 2 ≤ ENNReal.ofReal (M * R ^ d))
    (i : Fin d) {r ε T : ℝ} (hr : R₀ ≤ r) (hε : 0 < ε) (hεT : ε ≤ T) (hTr : T ≤ r ^ 2) :
    ∫⁻ x in ball 0 r, ‖heatGradWindow ε T i F x‖ₑ ^ 2 ≤
      ENNReal.ofReal (smallTimeConst d * M * T * r ^ d) := by
  have hT0 : 0 < T := lt_of_lt_of_le hε hεT
  have hc₁0 := smallTimeGradConst_nonneg d
  have hGc := smallTimeGaussConst_nonneg d
  have hI : ∫⁻ t in Icc ε T, smallTimeWeight d t ≤
      ENNReal.ofReal (smallTimeGradConst d * (2 * T ^ (1 / 2 : ℝ))) :=
    lintegral_Icc_rpow_neg_half_le hε hεT hc₁0
  have hpt : ∀ x, ‖heatGradWindow ε T i F x‖ₑ ^ 2 ≤
      ENNReal.ofReal (smallTimeGradConst d * (2 * T ^ (1 / 2 : ℝ))) *
        ∫⁻ t in Icc ε T, smallTimeWeight d t * heatConvEnorm F 2 t x := by
    intro x
    have h1 : ‖heatGradWindow ε T i F x‖ₑ ≤
        ∫⁻ t in Icc ε T, smallTimeWeight d t * heatConvEnorm F 1 t x :=
      (enorm_integral_le_lintegral_enorm _).trans (setLIntegral_mono' measurableSet_Icc
        fun t ht => enorm_heatGradConv_le (lt_of_lt_of_le hε ht.1) i F x)
    have h2 := sq_lintegral_mul_le (μ := volume.restrict (Icc ε T))
      (measurable_smallTimeWeight d).aemeasurable
      (measurable_heatConvEnorm_time hFm 1 x).aemeasurable
    calc ‖heatGradWindow ε T i F x‖ₑ ^ 2
        ≤ (∫⁻ t in Icc ε T, smallTimeWeight d t * heatConvEnorm F 1 t x) ^ 2 := by gcongr
      _ ≤ (∫⁻ t in Icc ε T, smallTimeWeight d t) *
          ∫⁻ t in Icc ε T, smallTimeWeight d t * heatConvEnorm F 1 t x ^ 2 := h2
      _ ≤ _ := by
          refine mul_le_mul' hI (setLIntegral_mono' measurableSet_Icc fun t ht => ?_)
          exact mul_le_mul' le_rfl (heatConvEnorm_sq_le (lt_of_lt_of_le hε ht.1) hFm x)
  have hw2 : Measurable (fun p : Vec d × ℝ => smallTimeWeight d p.2) :=
    (measurable_smallTimeWeight d).comp measurable_snd
  have hswapm : Measurable (fun p : Vec d × ℝ =>
      smallTimeWeight d p.2 * heatConvEnorm F 2 p.2 p.1) :=
    hw2.mul (measurable_heatConvEnorm_swap hFm 2)
  have hT2 : (T ^ (1 / 2 : ℝ)) ^ 2 = T := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]
    norm_num
  calc ∫⁻ x in ball 0 r, ‖heatGradWindow ε T i F x‖ₑ ^ 2
      ≤ ∫⁻ x in ball 0 r, ENNReal.ofReal (smallTimeGradConst d * (2 * T ^ (1 / 2 : ℝ))) *
          ∫⁻ t in Icc ε T, smallTimeWeight d t * heatConvEnorm F 2 t x := lintegral_mono hpt
    _ = ENNReal.ofReal (smallTimeGradConst d * (2 * T ^ (1 / 2 : ℝ))) *
          ∫⁻ x in ball 0 r, ∫⁻ t in Icc ε T, smallTimeWeight d t * heatConvEnorm F 2 t x :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (smallTimeGradConst d * (2 * T ^ (1 / 2 : ℝ))) *
          ∫⁻ t in Icc ε T, ∫⁻ x in ball 0 r, smallTimeWeight d t * heatConvEnorm F 2 t x := by
        rw [lintegral_lintegral_swap hswapm.aemeasurable]
    _ = ENNReal.ofReal (smallTimeGradConst d * (2 * T ^ (1 / 2 : ℝ))) *
          ∫⁻ t in Icc ε T, smallTimeWeight d t * ∫⁻ x in ball 0 r, heatConvEnorm F 2 t x := by
        congr 1
        refine lintegral_congr fun t => ?_
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (smallTimeGradConst d * (2 * T ^ (1 / 2 : ℝ))) *
          ∫⁻ t in Icc ε T, smallTimeWeight d t * ENNReal.ofReal ((2 : ℝ) ^ ((d : ℝ) / 2) *
            Real.exp (1 / 16) * (smallTimeGaussConst d * M * r ^ d)) :=
        mul_le_mul' le_rfl (setLIntegral_mono' measurableSet_Icc fun t ht =>
          mul_le_mul' le_rfl (lintegral_ball_heatConvEnorm_sq_le hFm hM hR₀ hgrowth hr
            (lt_of_lt_of_le hε ht.1) (ht.2.trans hTr)))
    _ = ENNReal.ofReal (smallTimeGradConst d * (2 * T ^ (1 / 2 : ℝ))) *
          ((∫⁻ t in Icc ε T, smallTimeWeight d t) * ENNReal.ofReal ((2 : ℝ) ^ ((d : ℝ) / 2) *
            Real.exp (1 / 16) * (smallTimeGaussConst d * M * r ^ d))) := by
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (smallTimeGradConst d * (2 * T ^ (1 / 2 : ℝ))) *
          (ENNReal.ofReal (smallTimeGradConst d * (2 * T ^ (1 / 2 : ℝ))) *
            ENNReal.ofReal ((2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (1 / 16) *
              (smallTimeGaussConst d * M * r ^ d))) :=
        mul_le_mul' le_rfl (mul_le_mul' hI le_rfl)
    _ = ENNReal.ofReal (smallTimeConst d * M * T * r ^ d) := by
        have hr0 : 0 < r := lt_of_lt_of_le hR₀ hr
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        unfold smallTimeConst
        calc smallTimeGradConst d * (2 * T ^ (1 / 2 : ℝ)) *
              (smallTimeGradConst d * (2 * T ^ (1 / 2 : ℝ)) *
                ((2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (1 / 16) * (smallTimeGaussConst d * M * r ^ d)))
            = 4 * smallTimeGradConst d ^ 2 * ((2 : ℝ) ^ ((d : ℝ) / 2) *
                Real.exp (1 / 16) * smallTimeGaussConst d) * M * (T ^ (1 / 2 : ℝ)) ^ 2 *
                r ^ d := by ring
          _ = _ := by rw [hT2]

end SmallTime

end EinsteinFull.Homogenization
