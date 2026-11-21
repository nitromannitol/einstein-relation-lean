import EinsteinFull.Homogenization.KernelConvolutionHessian
import EinsteinRelation.Correctors.HeatGradientConvolution
import EinsteinRelation.Correctors.HeatConvolutionMeasurability
import Homogenization.Sobolev.Foundations.DifferenceQuotient

/-!
# The time-truncated heat Hessian on smooth functions

For `0 < ε₁ ≤ ε₂` and a smooth compactly supported `ψ`, the time-truncated heat Hessian
`∫_{ε₁}^{ε₂} ∂ⱼ∂ᵢΦ_t * ψ dt` of the heat formula (6.7) in Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*, is the convolution of
`∂ⱼ∂ᵢψ` with the time-integrated kernel `κ = ∫_{ε₁}^{ε₂} Φ_t dt`, and its trace is
`Φ_{ε₂} * ψ - Φ_{ε₁} * ψ` by the heat equation. The `L²` identity for second derivatives of
convolutions then gives
`∑ᵢⱼ ‖∫_{ε₁}^{ε₂} ∂ⱼ∂ᵢΦ_t * ψ dt‖₂² = ‖Φ_{ε₂} * ψ - Φ_{ε₁} * ψ‖₂²`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace EinsteinFull.Homogenization

open EinsteinRelation EinsteinRelation.Correctors

variable {d : ℕ}

/-- The heat semigroup `Φ_t * f`. -/
noncomputable def heatConv (t : ℝ) (f : Vec d → ℝ) (x : Vec d) : ℝ :=
  ∫ y, euclideanHeatKernel t (x - y) * f y

/-- Convolution with the mixed Hessian `∂ⱼ∂ᵢΦ_t`, in the form of the heat formula (6.7). -/
noncomputable def heatHessianConv (t : ℝ) (i j : Fin d) (f : Vec d → ℝ) (x : Vec d) : ℝ :=
  ∫ y, coordinateDerivative j (coordinateDerivative i (euclideanHeatKernel t)) (x - y) * f y

/-- The time-truncated heat Hessian `∫_{ε₁}^{ε₂} ∂ⱼ∂ᵢΦ_t * f dt`. -/
noncomputable def heatHessianWindow (ε₁ ε₂ : ℝ) (i j : Fin d) (f : Vec d → ℝ) (x : Vec d) : ℝ :=
  ∫ t in Icc ε₁ ε₂, heatHessianConv t i j f x

/-- The time-integrated heat kernel `∫_{ε₁}^{ε₂} Φ_t dt`. -/
noncomputable def heatWindowKernel (ε₁ ε₂ : ℝ) (z : Vec d) : ℝ :=
  ∫ t in Icc ε₁ ε₂, euclideanHeatKernel t z

theorem contDiff_coordinateDerivative {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (i : Fin d) : ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative i f) :=
  ((contDiff_infty_iff_fderiv.mp hf).2).clm_apply contDiff_const

theorem integrable_mul_of_hasCompactSupport_right {A B : Vec d → ℝ} (hA : Continuous A)
    (hB : Continuous B) (hBc : HasCompactSupport B) :
    Integrable (fun x => A x * B x) volume :=
  (hA.mul hB).integrable_of_hasCompactSupport hBc.mul_left

theorem integrable_mul_of_hasCompactSupport_left {A B : Vec d → ℝ} (hA : Continuous A)
    (hAc : HasCompactSupport A) (hB : Continuous B) :
    Integrable (fun x => A x * B x) volume :=
  (hA.mul hB).integrable_of_hasCompactSupport hAc.mul_right

theorem measurable_heatWindowKernel (ε₁ ε₂ : ℝ) :
    Measurable (heatWindowKernel (d := d) ε₁ ε₂) :=
  (measurable_euclideanHeatKernel_joint (d := d)).stronglyMeasurable.integral_prod_left.measurable

theorem lintegral_enorm_heatWindowKernel_le {ε₁ ε₂ : ℝ} (hε₁ : 0 < ε₁) :
    ∫⁻ z : Vec d, ‖heatWindowKernel ε₁ ε₂ z‖ₑ ≤ ENNReal.ofReal (ε₂ - ε₁) := by
  have hjoint : Measurable (Function.uncurry fun (t : ℝ) (z : Vec d) =>
      ‖euclideanHeatKernel t z‖ₑ) :=
    (measurable_euclideanHeatKernel_joint (d := d)).enorm
  calc ∫⁻ z : Vec d, ‖heatWindowKernel ε₁ ε₂ z‖ₑ
      ≤ ∫⁻ z : Vec d, ∫⁻ t in Icc ε₁ ε₂, ‖euclideanHeatKernel t z‖ₑ :=
        lintegral_mono fun z => enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ t in Icc ε₁ ε₂, ∫⁻ z : Vec d, ‖euclideanHeatKernel t z‖ₑ :=
        lintegral_lintegral_swap (hjoint.comp measurable_swap).aemeasurable
    _ = ∫⁻ _t in Icc ε₁ ε₂, 1 := by
        refine setLIntegral_congr_fun measurableSet_Icc fun t ht => ?_
        exact lintegral_enorm_euclideanHeatKernel (lt_of_lt_of_le hε₁ ht.1)
    _ = ENNReal.ofReal (ε₂ - ε₁) := by
        rw [setLIntegral_const, Real.volume_Icc, one_mul]

theorem lintegral_enorm_heatWindowKernel_ne_top {ε₁ ε₂ : ℝ} (hε₁ : 0 < ε₁) :
    ∫⁻ z : Vec d, ‖heatWindowKernel ε₁ ε₂ z‖ₑ ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (lintegral_enorm_heatWindowKernel_le hε₁)

theorem euclideanHeatKernel_le_of_le {ε t : ℝ} (hε : 0 < ε) (ht : ε ≤ t) (z : Vec d) :
    euclideanHeatKernel t z ≤ (4 * Real.pi * ε) ^ (-(d : ℝ) / 2) := by
  have ht0 : 0 < t := lt_of_lt_of_le hε ht
  unfold euclideanHeatKernel
  have hexp : Real.exp (-euclideanSq z / (4 * t)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ euclideanSq z := by
      unfold euclideanSq dot
      exact Finset.sum_nonneg fun l _ => mul_self_nonneg (z l)
    have : 0 < 4 * t := by positivity
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) this.le
  calc (4 * Real.pi * t) ^ (-(d : ℝ) / 2) * Real.exp (-euclideanSq z / (4 * t))
      ≤ (4 * Real.pi * t) ^ (-(d : ℝ) / 2) * 1 :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ ≤ (4 * Real.pi * ε) ^ (-(d : ℝ) / 2) := by
        rw [mul_one]
        exact Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [Real.pi_pos])
          (by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith)

/-- **Fubini for the time window**: averaging heat smoothings over the window is convolution
with the time-integrated kernel. -/
theorem setIntegral_heatConv_eq_kconv {ε₁ ε₂ : ℝ} (hε₁ : 0 < ε₁) {F : Vec d → ℝ}
    (hF : Continuous F) (hFc : HasCompactSupport F) (x : Vec d) :
    ∫ t in Icc ε₁ ε₂, heatConv t F x = kconv (heatWindowKernel ε₁ ε₂) F x := by
  rw [kconv_apply]
  set C := (4 * Real.pi * ε₁) ^ (-(d : ℝ) / 2) with hC
  have hFi : Integrable F volume := hF.integrable_of_hasCompactSupport hFc
  have hmeas : Measurable (Function.uncurry fun (t : ℝ) (y : Vec d) =>
      euclideanHeatKernel t (x - y) * F y) :=
    ((measurable_euclideanHeatKernel_joint (d := d)).comp
      (measurable_fst.prodMk (measurable_const.sub measurable_snd))).mul
      (hF.measurable.comp measurable_snd)
  have hint : Integrable (Function.uncurry fun (t : ℝ) (y : Vec d) =>
      euclideanHeatKernel t (x - y) * F y) ((volume.restrict (Icc ε₁ ε₂)).prod volume) := by
    have hdom : Integrable (fun p : ℝ × Vec d => C * |F p.2|)
        ((volume.restrict (Icc ε₁ ε₂)).prod volume) := by
      have h1 : Integrable (fun _ : ℝ => C) (volume.restrict (Icc ε₁ ε₂)) := by
        have : IsFiniteMeasure (volume.restrict (Icc ε₁ ε₂)) := by
          rw [isFiniteMeasure_restrict]
          exact (Real.volume_Icc (a := ε₁) (b := ε₂)).symm ▸ ENNReal.ofReal_ne_top
        exact integrable_const C
      exact h1.mul_prod hFi.abs
    refine hdom.mono' hmeas.aestronglyMeasurable ?_
    have hprod : (volume.restrict (Icc ε₁ ε₂)).prod (volume : Measure (Vec d)) =
        ((volume : Measure ℝ).prod (volume : Measure (Vec d))).restrict (Icc ε₁ ε₂ ×ˢ univ) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    rw [hprod]
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod MeasurableSet.univ)] with p hp
    simp only [Function.uncurry, Real.norm_eq_abs, abs_mul]
    have ht : ε₁ ≤ p.1 := hp.1.1
    rw [abs_of_nonneg (euclideanHeatKernel_nonneg (by linarith) _)]
    exact mul_le_mul_of_nonneg_right (euclideanHeatKernel_le_of_le hε₁ ht _) (abs_nonneg _)
  rw [show (fun t => heatConv t F x) = fun t => ∫ y, euclideanHeatKernel t (x - y) * F y from rfl,
    integral_integral_swap hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [heatWindowKernel]
  rw [integral_mul_const]

/-- Two integrations by parts move the heat-kernel Hessian onto a smooth compactly supported
function. -/
theorem heatHessianConv_eq_heatConv {t : ℝ} (ht : 0 < t) (i j : Fin d) {ψ : Vec d → ℝ}
    (hψ : IsSmoothCompact ψ) (x : Vec d) :
    heatHessianConv t i j ψ x =
      heatConv t (coordinateDerivative j (coordinateDerivative i ψ)) x := by
  set h : Vec d → ℝ := fun w => euclideanHeatKernel t (x - w) with hh
  have hhs : ContDiff ℝ (⊤ : ℕ∞) h :=
    (contDiff_euclideanHeatKernel t).comp (contDiff_const.sub contDiff_id)
  have hih : ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative i h) := contDiff_coordinateDerivative hhs i
  have hjψ := hψ.coordinateDerivative j
  have hijψ := hjψ.coordinateDerivative i
  have heven : ∀ y, coordinateDerivative j (coordinateDerivative i (euclideanHeatKernel t))
      (x - y) = coordinateDerivative j (coordinateDerivative i h) y := by
    intro y
    rw [hh, centeredHeatKernel_secondDerivative t i j y x, heatHessian_eq ht,
      show y - x = -(x - y) by abel]
    simp only [euclideanHeatKernel_neg, Pi.neg_apply, neg_mul_neg]
  have hdiff : ∀ {g : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) g → Differentiable ℝ g := fun hg =>
    hg.differentiable (by simp)
  have h1 := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := ψ) (g := coordinateDerivative i h) (v := unitVector j)
    (integrable_mul_of_hasCompactSupport_left hjψ.1.continuous hjψ.2 hih.continuous)
    (integrable_mul_of_hasCompactSupport_left hψ.1.continuous hψ.2
      (contDiff_coordinateDerivative hih j).continuous)
    (integrable_mul_of_hasCompactSupport_left hψ.1.continuous hψ.2 hih.continuous)
    (fun y _ => hdiff hψ.1 y) (fun y _ => hdiff hih y)
  have h2 := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := coordinateDerivative j ψ) (g := h) (v := unitVector i)
    (integrable_mul_of_hasCompactSupport_left hijψ.1.continuous hijψ.2 hhs.continuous)
    (integrable_mul_of_hasCompactSupport_left hjψ.1.continuous hjψ.2 hih.continuous)
    (integrable_mul_of_hasCompactSupport_left hjψ.1.continuous hjψ.2 hhs.continuous)
    (fun y _ => hdiff hjψ.1 y) (fun y _ => hdiff hhs y)
  change ∫ y, ψ y * coordinateDerivative j (coordinateDerivative i h) y =
    -∫ y, coordinateDerivative j ψ y * coordinateDerivative i h y at h1
  change ∫ y, coordinateDerivative j ψ y * coordinateDerivative i h y =
    -∫ y, coordinateDerivative i (coordinateDerivative j ψ) y * h y at h2
  unfold heatHessianConv heatConv
  simp_rw [heven]
  rw [coordinateDerivative_comm hψ.1 j i]
  calc ∫ y, coordinateDerivative j (coordinateDerivative i h) y * ψ y
      = ∫ y, ψ y * coordinateDerivative j (coordinateDerivative i h) y := by
        simp_rw [mul_comm]
    _ = ∫ y, h y * coordinateDerivative i (coordinateDerivative j ψ) y := by
        rw [h1, h2, neg_neg]
        simp_rw [mul_comm]

theorem heatHessianWindow_eq_kconv {ε₁ ε₂ : ℝ} (hε₁ : 0 < ε₁) (i j : Fin d) {ψ : Vec d → ℝ}
    (hψ : IsSmoothCompact ψ) :
    heatHessianWindow ε₁ ε₂ i j ψ =
      kconv (heatWindowKernel ε₁ ε₂) (coordinateDerivative j (coordinateDerivative i ψ)) := by
  funext x
  have hD := (hψ.coordinateDerivative i).coordinateDerivative j
  rw [heatHessianWindow, ← setIntegral_heatConv_eq_kconv hε₁ hD.1.continuous hD.2 x]
  exact setIntegral_congr_fun measurableSet_Icc fun t ht =>
    heatHessianConv_eq_heatConv (lt_of_lt_of_le hε₁ ht.1) i j hψ x

theorem heatConv_eq_heatKernelConvolution {t : ℝ} (ht : 0 < t) (F : Vec d → ℝ) (x : Vec d) :
    heatConv t F x = heatKernelConvolution t F x := by
  simp only [heatConv, heatKernelConvolution, ht.ne', ↓reduceIte]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only
  rw [mul_comm, show x - y = -(y - x) by abel, euclideanHeatKernel_neg]

/-- **The heat equation in the time window**: the trace of the time-truncated heat Hessian is
`Φ_{ε₂} * ψ - Φ_{ε₁} * ψ`. -/
theorem sum_kconv_laplacian {ε₁ ε₂ : ℝ} (hε₁ : 0 < ε₁) (hε : ε₁ ≤ ε₂) {ψ : Vec d → ℝ}
    (hψ : IsSmoothCompact ψ) (x : Vec d) :
    ∑ i, kconv (heatWindowKernel ε₁ ε₂) (coordinateDerivative i (coordinateDerivative i ψ)) x =
      heatConv ε₂ ψ x - heatConv ε₁ ψ x := by
  have hD : ∀ i, IsSmoothCompact (coordinateDerivative i (coordinateDerivative i ψ)) :=
    fun i => (hψ.coordinateDerivative i).coordinateDerivative i
  have hψ2 : ContDiff ℝ 2 ψ := hψ.1.of_le (by norm_cast)
  have hlap : coordLaplacian ψ = fun y => ∑ i, coordinateDerivative i (coordinateDerivative i ψ) y :=
    rfl
  have hsum : ∑ i, kconv (heatWindowKernel ε₁ ε₂)
      (coordinateDerivative i (coordinateDerivative i ψ)) x =
      kconv (heatWindowKernel ε₁ ε₂) (coordLaplacian ψ) x := by
    simp_rw [kconv_apply, hlap, Finset.mul_sum]
    have hκint : Integrable (heatWindowKernel (d := d) ε₁ ε₂) volume :=
      ⟨(measurable_heatWindowKernel ε₁ ε₂).aestronglyMeasurable,
        (lintegral_enorm_heatWindowKernel_ne_top hε₁).lt_top⟩
    rw [integral_finsetSum _ fun i _ => ?_]
    simpa only [smul_eq_mul] using
      (hκint.comp_sub_left x).locallyIntegrable.integrable_smul_right_of_hasCompactSupport
        (hD i).1.continuous (hD i).2
  rw [hsum, ← setIntegral_heatConv_eq_kconv hε₁ (continuous_coordLaplacian hψ2)
    (hasCompactSupport_coordLaplacian hψ.2) x]
  have hcont := continuousOn_heatKernelConvolution (continuous_coordLaplacian hψ2)
    (hasCompactSupport_coordLaplacian hψ.2) x
  have hii : ∀ T, 0 ≤ T → IntervalIntegrable
      (fun t => heatKernelConvolution t (coordLaplacian ψ) x) volume 0 T := fun T hT =>
    (hcont.mono (show uIcc 0 T ⊆ Ici 0 by
      rw [uIcc_of_le hT]; exact fun _ hx => hx.1)).intervalIntegrable
  have h₂ := heatKernelConvolution_sub_initial hψ2 hψ.2 x (le_of_lt (lt_of_lt_of_le hε₁ hε))
  have h₁ := heatKernelConvolution_sub_initial hψ2 hψ.2 x hε₁.le
  rw [heatConv_eq_heatKernelConvolution (lt_of_lt_of_le hε₁ hε),
    heatConv_eq_heatKernelConvolution hε₁,
    show heatKernelConvolution ε₂ ψ x - heatKernelConvolution ε₁ ψ x =
      (heatKernelConvolution ε₂ ψ x - ψ x) - (heatKernelConvolution ε₁ ψ x - ψ x) by ring,
    h₂, h₁, intervalIntegral.integral_interval_sub_left (hii _ (by linarith)) (hii _ hε₁.le),
    intervalIntegral.integral_of_le hε, ← integral_Icc_eq_integral_Ioc]
  exact setIntegral_congr_fun measurableSet_Icc fun t ht =>
    heatConv_eq_heatKernelConvolution (lt_of_lt_of_le hε₁ ht.1) _ x

theorem memLp_heatHessianWindow {ε₁ ε₂ : ℝ} (hε₁ : 0 < ε₁) (i j : Fin d) {ψ : Vec d → ℝ}
    (hψ : IsSmoothCompact ψ) : MemLp (heatHessianWindow ε₁ ε₂ i j ψ) 2 volume := by
  rw [heatHessianWindow_eq_kconv hε₁ i j hψ]
  exact memLp_kconv (measurable_heatWindowKernel ε₁ ε₂)
    (lintegral_enorm_heatWindowKernel_ne_top hε₁)
    ((hψ.coordinateDerivative i).coordinateDerivative j)

theorem memLp_heatConv {t : ℝ} (ht : 0 < t) {f : Vec d → ℝ} (hf : Measurable f)
    (hf2 : MemLp f 2 volume) : MemLp (heatConv t f) 2 volume := by
  have h := memLp_kernel (measurable_euclideanHeatKernel (d := d) t)
    (by rw [lintegral_enorm_euclideanHeatKernel ht]; exact ENNReal.one_ne_top) hf hf2
  exact h

/-- **The `L²` identity for the time-truncated heat Hessian** on smooth compactly supported
functions. -/
theorem sum_integral_heatHessianWindow_sq {ε₁ ε₂ : ℝ} (hε₁ : 0 < ε₁) (hε : ε₁ ≤ ε₂)
    {ψ : Vec d → ℝ} (hψ : IsSmoothCompact ψ) :
    ∑ i, ∑ j, ∫ x, heatHessianWindow ε₁ ε₂ i j ψ x ^ 2 =
      ∫ x, (heatConv ε₂ ψ x - heatConv ε₁ ψ x) ^ 2 := by
  simp_rw [heatHessianWindow_eq_kconv hε₁ _ _ hψ]
  rw [Finset.sum_comm, sum_integral_kconv_sq (measurable_heatWindowKernel ε₁ ε₂)
    (lintegral_enorm_heatWindowKernel_ne_top hε₁) hψ]
  simp_rw [sum_kconv_laplacian hε₁ hε hψ]

/-- Each entry of the time-truncated heat Hessian of a smooth compactly supported function is
bounded in `L²` by the difference of its heat smoothings at the two ends of the window. -/
theorem eLpNorm_heatHessianWindow_le_of_smooth {ε₁ ε₂ : ℝ} (hε₁ : 0 < ε₁) (hε : ε₁ ≤ ε₂)
    (i j : Fin d) {ψ : Vec d → ℝ} (hψ : IsSmoothCompact ψ) :
    eLpNorm (heatHessianWindow ε₁ ε₂ i j ψ) 2 volume ≤
      eLpNorm (fun x => heatConv ε₂ ψ x - heatConv ε₁ ψ x) 2 volume := by
  have hm := memLp_heatHessianWindow (ε₂ := ε₂) hε₁ i j hψ
  have hψm := hψ.1.continuous.measurable
  have hdiff : MemLp (fun x => heatConv ε₂ ψ x - heatConv ε₁ ψ x) 2 volume :=
    (memLp_heatConv (lt_of_lt_of_le hε₁ hε) hψm hψ.memLp).sub (memLp_heatConv hε₁ hψm hψ.memLp)
  have hsq : ∫ x, heatHessianWindow ε₁ ε₂ i j ψ x ^ 2 ≤
      ∫ x, (heatConv ε₂ ψ x - heatConv ε₁ ψ x) ^ 2 := by
    rw [← sum_integral_heatHessianWindow_sq hε₁ hε hψ]
    have hnn : ∀ a b : Fin d, 0 ≤ ∫ x, heatHessianWindow ε₁ ε₂ a b ψ x ^ 2 := fun a b =>
      integral_nonneg fun x => sq_nonneg _
    calc ∫ x, heatHessianWindow ε₁ ε₂ i j ψ x ^ 2
        ≤ ∑ b, ∫ x, heatHessianWindow ε₁ ε₂ i b ψ x ^ 2 :=
          Finset.single_le_sum (f := fun b => ∫ x, heatHessianWindow ε₁ ε₂ i b ψ x ^ 2)
            (fun b _ => hnn i b) (Finset.mem_univ j)
      _ ≤ ∑ a, ∑ b, ∫ x, heatHessianWindow ε₁ ε₂ a b ψ x ^ 2 :=
          Finset.single_le_sum (f := fun a => ∑ b, ∫ x, heatHessianWindow ε₁ ε₂ a b ψ x ^ 2)
            (fun a _ => Finset.sum_nonneg fun b _ => hnn a b) (Finset.mem_univ i)
  rw [← _root_.Homogenization.toReal_eLpNorm_two_sq_eq_integral_sq hm,
    ← _root_.Homogenization.toReal_eLpNorm_two_sq_eq_integral_sq hdiff] at hsq
  rw [← ENNReal.ofReal_toReal hm.eLpNorm_ne_top, ← ENNReal.ofReal_toReal hdiff.eLpNorm_ne_top]
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_iff_left₀ ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    two_ne_zero |>.mp hsq)

end EinsteinFull.Homogenization
