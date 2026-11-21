import EinsteinFull.Homogenization.HeatHessianSmoothL2
import Mathlib.Analysis.Normed.Lp.SmoothApprox

/-!
# The time-truncated heat Hessian on `L²`

For `f ∈ L²(ℝ^d)` and `0 < ε₁ ≤ ε₂`, the time-truncated heat Hessian
`W f = ∫_{ε₁}^{ε₂} ∂ⱼ∂ᵢΦ_t * f dt` of the heat formula (6.7) in Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*, satisfies
`‖W f‖₂ ≤ ‖Φ_{ε₂} * f - Φ_{ε₁} * f‖₂`. The identity for smooth compactly supported functions
extends by density, using the crude bound `‖W f‖₂ ≤ C(ε₁, ε₂) ‖f‖₂`. Since the heat semigroup is
continuous at time zero on `L²`, the truncations are Cauchy in `L²` as both endpoints tend to
zero. This is the Calderón–Zygmund part of the existence of the heat-selected flux corrector.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace EinsteinFull.Homogenization

open EinsteinRelation EinsteinRelation.Correctors

variable {d : ℕ}

theorem euclideanSq_nonneg (z : Vec d) : 0 ≤ euclideanSq z := by
  unfold euclideanSq dot
  exact Finset.sum_nonneg fun l _ => mul_self_nonneg (z l)

/-- Comparison of heat kernels at two times. -/
theorem euclideanHeatKernel_le_mul {s S : ℝ} (hs : 0 < s) (hsS : s ≤ S) (z : Vec d) :
    euclideanHeatKernel s z ≤ (S / s) ^ ((d : ℝ) / 2) * euclideanHeatKernel S z := by
  have hS : 0 < S := lt_of_lt_of_le hs hsS
  have hz := euclideanSq_nonneg z
  have hexp : Real.exp (-euclideanSq z / (4 * s)) ≤ Real.exp (-euclideanSq z / (4 * S)) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left hz (by positivity) (by linarith)
  have hpow : (4 * Real.pi * s) ^ (-(d : ℝ) / 2) =
      (S / s) ^ ((d : ℝ) / 2) * (4 * Real.pi * S) ^ (-(d : ℝ) / 2) := by
    have h1 : 4 * Real.pi * s = (s / S) * (4 * Real.pi * S) := by field_simp
    rw [h1, Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    rw [show -(d : ℝ) / 2 = -((d : ℝ) / 2) by ring, Real.rpow_neg (by positivity),
      ← Real.inv_rpow (by positivity), inv_div]
  unfold euclideanHeatKernel
  rw [hpow, mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp (by positivity)) (by positivity)

/-- The constant dominating the heat-kernel Hessian on a time window. -/
noncomputable def windowHessianConst (d : ℕ) (ε₁ ε₂ : ℝ) : ℝ :=
  (2 : ℝ) ^ ((d : ℝ) / 2) * (2 / ε₁) * (ε₂ / ε₁) ^ ((d : ℝ) / 2)

theorem windowHessianConst_nonneg {ε₁ : ℝ} (hε₁ : 0 < ε₁) {ε₂ : ℝ} (hε : ε₁ ≤ ε₂) :
    0 ≤ windowHessianConst d ε₁ ε₂ := by
  have : 0 < ε₂ := lt_of_lt_of_le hε₁ hε
  unfold windowHessianConst
  positivity

/-- On the window `[ε₁, ε₂]` the heat-kernel Hessian is dominated by one Gaussian. -/
theorem abs_heatHessian_le_window {ε₁ ε₂ t : ℝ} (hε₁ : 0 < ε₁) (ht : t ∈ Icc ε₁ ε₂)
    (i j : Fin d) (z : Vec d) :
    |coordinateDerivative j (coordinateDerivative i (euclideanHeatKernel t)) z| ≤
      windowHessianConst d ε₁ ε₂ * euclideanHeatKernel (2 * ε₂) z := by
  have ht0 : 0 < t := lt_of_lt_of_le hε₁ ht.1
  have h1 := abs_heatHessian_le ht0 i j z
  have h2 := euclideanHeatKernel_le_mul (d := d) (s := 2 * t) (S := 2 * ε₂) (by positivity)
    (by linarith [ht.2]) z
  have h3 : (2 * ε₂ / (2 * t)) ^ ((d : ℝ) / 2) ≤ (ε₂ / ε₁) ^ ((d : ℝ) / 2) := by
    rw [mul_div_mul_left _ _ two_ne_zero]
    exact Real.rpow_le_rpow (div_nonneg (by linarith [ht.1, ht.2]) ht0.le)
      (div_le_div_of_nonneg_left (by linarith [ht.2, ht.1]) hε₁ ht.1) (by positivity)
  have h4 : 2 / t ≤ 2 / ε₁ := div_le_div_of_nonneg_left (by norm_num) hε₁ ht.1
  have hK := euclideanHeatKernel_nonneg (d := d) (t := 2 * ε₂) (by linarith [ht.2]) z
  calc _ ≤ (2 : ℝ) ^ ((d : ℝ) / 2) * (2 / t) * euclideanHeatKernel (2 * t) z := h1
    _ ≤ (2 : ℝ) ^ ((d : ℝ) / 2) * (2 / t) *
        ((2 * ε₂ / (2 * t)) ^ ((d : ℝ) / 2) * euclideanHeatKernel (2 * ε₂) z) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ (2 : ℝ) ^ ((d : ℝ) / 2) * (2 / ε₁) *
        ((ε₂ / ε₁) ^ ((d : ℝ) / 2) * euclideanHeatKernel (2 * ε₂) z) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h4 (by positivity))
          (mul_le_mul_of_nonneg_right h3 hK)
          (mul_nonneg (Real.rpow_nonneg (div_nonneg (by linarith [ht.1, ht.2]) (by linarith)) _) hK)
          (by positivity)
    _ = windowHessianConst d ε₁ ε₂ * euclideanHeatKernel (2 * ε₂) z := by
        unfold windowHessianConst
        ring

theorem euclideanHeatKernel_le_const {t : ℝ} (ht : 0 < t) (z : Vec d) :
    euclideanHeatKernel t z ≤ (4 * Real.pi * t) ^ (-(d : ℝ) / 2) :=
  euclideanHeatKernel_le_of_le ht le_rfl z

theorem memLp_euclideanHeatKernel {t : ℝ} (ht : 0 < t) :
    MemLp (euclideanHeatKernel (d := d) t) 2 volume := by
  have hm := (measurable_euclideanHeatKernel (d := d) t).aestronglyMeasurable (μ := volume)
  refine (memLp_two_iff_integrable_sq hm).2 ?_
  refine ((integrable_euclideanHeatKernel (d := d) ht).const_mul
    ((4 * Real.pi * t) ^ (-(d : ℝ) / 2))).mono' (hm.pow 2) (Filter.Eventually.of_forall
      fun z => ?_)
  have h0 := euclideanHeatKernel_nonneg (d := d) ht.le z
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), sq]
  exact mul_le_mul_of_nonneg_right (euclideanHeatKernel_le_const ht z) h0

/-- A square-integrable kernel against a square-integrable function, at every center. -/
theorem integrable_kernel_mul {k f : Vec d → ℝ} (hk : MemLp k 2 volume)
    (hf : MemLp f 2 volume) (x : Vec d) :
    Integrable (fun y => k (x - y) * f y) volume :=
  (hk.comp_measurePreserving (Measure.measurePreserving_sub_left volume x)).integrable_mul hf

theorem memLp_heatHessian {t : ℝ} (ht : 0 < t) (i j : Fin d) :
    MemLp (coordinateDerivative j (coordinateDerivative i (euclideanHeatKernel (d := d) t)))
      2 volume := by
  refine ((memLp_euclideanHeatKernel (d := d) (t := 2 * t) (by positivity)).const_mul
    ((2 : ℝ) ^ ((d : ℝ) / 2) * (2 / t))).of_le
    (measurable_heatHessian ht i j).aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤
    (2 : ℝ) ^ ((d : ℝ) / 2) * (2 / t)),
    abs_of_nonneg (euclideanHeatKernel_nonneg (by positivity) z)]
  exact abs_heatHessian_le ht i j z

/-- The explicit heat-kernel Hessian, jointly in time and space. -/
noncomputable def heatHessianKernel (t : ℝ) (i j : Fin d) (z : Vec d) : ℝ :=
  euclideanHeatKernel t z * (z i * z j / (4 * t ^ 2) - (if i = j then 1 / (2 * t) else 0))

theorem measurable_heatHessianKernel (i j : Fin d) :
    Measurable (fun p : ℝ × Vec d => heatHessianKernel p.1 i j p.2) := by
  unfold heatHessianKernel
  refine (measurable_euclideanHeatKernel_joint (d := d)).mul ?_
  by_cases hij : i = j
  · simp only [hij, ↓reduceIte]
    fun_prop
  · simp only [hij, ↓reduceIte]
    fun_prop

theorem heatHessianConv_eq_kernel {t : ℝ} (ht : 0 < t) (i j : Fin d) (f : Vec d → ℝ)
    (x : Vec d) :
    heatHessianConv t i j f x = ∫ y, heatHessianKernel t i j (x - y) * f y := by
  rw [heatHessianConv, heatHessian_eq ht]
  rfl

theorem stronglyMeasurable_heatHessianKernelConv (i j : Fin d) {f : Vec d → ℝ}
    (hf : Measurable f) :
    StronglyMeasurable (fun p : ℝ × Vec d => ∫ y, heatHessianKernel p.1 i j (p.2 - y) * f y) :=
  (((measurable_heatHessianKernel i j).comp ((measurable_fst.comp measurable_fst).prodMk
    ((measurable_snd.comp measurable_fst).sub measurable_snd))).mul
      (hf.comp measurable_snd)).stronglyMeasurable.integral_prod_right'

/-- The time-truncated heat Hessian of a measurable function is strongly measurable. -/
theorem stronglyMeasurable_heatHessianWindow {ε₁ ε₂ : ℝ} (hε₁ : 0 < ε₁) (i j : Fin d)
    {f : Vec d → ℝ} (hf : Measurable f) :
    StronglyMeasurable (heatHessianWindow ε₁ ε₂ i j f) := by
  have h : heatHessianWindow ε₁ ε₂ i j f = fun x =>
      ∫ t in Icc ε₁ ε₂, ∫ y, heatHessianKernel t i j (x - y) * f y := by
    funext x
    exact setIntegral_congr_fun measurableSet_Icc fun t ht =>
      heatHessianConv_eq_kernel (lt_of_lt_of_le hε₁ ht.1) i j f x
  rw [h]
  exact (stronglyMeasurable_heatHessianKernelConv i j hf).integral_prod_left

theorem integrable_heatHessianConv_mul {t : ℝ} (ht : 0 < t) (i j : Fin d) {f : Vec d → ℝ}
    (hf : MemLp f 2 volume) (x : Vec d) :
    Integrable (fun y => coordinateDerivative j (coordinateDerivative i
      (euclideanHeatKernel t)) (x - y) * f y) volume :=
  integrable_kernel_mul (memLp_heatHessian ht i j) hf x

/-- On the window, the Hessian convolution is dominated by one Gaussian smoothing of `|f|`. -/
theorem abs_heatHessianConv_le_window {ε₁ ε₂ t : ℝ} (hε₁ : 0 < ε₁) (ht : t ∈ Icc ε₁ ε₂)
    (i j : Fin d) {f : Vec d → ℝ} (hf : MemLp f 2 volume) (x : Vec d) :
    |heatHessianConv t i j f x| ≤
      windowHessianConst d ε₁ ε₂ * ∫ y, euclideanHeatKernel (2 * ε₂) (x - y) * |f y| := by
  have hε₂ : 0 < 2 * ε₂ := by linarith [ht.1, ht.2]
  have hint := integrable_kernel_mul (memLp_euclideanHeatKernel (d := d) hε₂) hf.abs x
  rw [← integral_const_mul]
  refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun y => abs_nonneg _) (hint.const_mul _)
    (Filter.Eventually.of_forall fun y => ?_))
  simp only
  rw [abs_mul, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (abs_heatHessian_le_window hε₁ ht i j _) (abs_nonneg _)

theorem integrableOn_heatHessianConv {ε₁ ε₂ : ℝ} (hε₁ : 0 < ε₁) (i j : Fin d)
    {f : Vec d → ℝ} (hfm : Measurable f) (hf : MemLp f 2 volume) (x : Vec d) :
    IntegrableOn (fun t => heatHessianConv t i j f x) (Icc ε₁ ε₂) volume := by
  have hfin : IsFiniteMeasure (volume.restrict (Icc ε₁ ε₂)) := by
    rw [isFiniteMeasure_restrict]
    exact (Real.volume_Icc (a := ε₁) (b := ε₂)).symm ▸ ENNReal.ofReal_ne_top
  have hmeas : AEStronglyMeasurable (fun t => heatHessianConv t i j f x)
      (volume.restrict (Icc ε₁ ε₂)) := by
    have hs : StronglyMeasurable (fun t => ∫ y, heatHessianKernel t i j (x - y) * f y) :=
      (stronglyMeasurable_heatHessianKernelConv i j hfm).comp_measurable
        (measurable_id.prodMk measurable_const)
    refine hs.aestronglyMeasurable.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (heatHessianConv_eq_kernel (lt_of_lt_of_le hε₁ ht.1) i j f x).symm
  refine (integrable_const (windowHessianConst d ε₁ ε₂ *
    ∫ y, euclideanHeatKernel (2 * ε₂) (x - y) * |f y|)).mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [Real.norm_eq_abs]
  exact abs_heatHessianConv_le_window hε₁ ht i j hf x

/-- Linearity of the time-truncated heat Hessian on `L²`. -/
theorem heatHessianWindow_sub {ε₁ ε₂ : ℝ} (hε₁ : 0 < ε₁) (i j : Fin d) {f g : Vec d → ℝ}
    (hfm : Measurable f) (hf : MemLp f 2 volume) (hgm : Measurable g) (hg : MemLp g 2 volume)
    (x : Vec d) :
    heatHessianWindow ε₁ ε₂ i j (f - g) x =
      heatHessianWindow ε₁ ε₂ i j f x - heatHessianWindow ε₁ ε₂ i j g x := by
  unfold heatHessianWindow
  rw [← integral_sub (integrableOn_heatHessianConv hε₁ i j hfm hf x)
    (integrableOn_heatHessianConv hε₁ i j hgm hg x)]
  refine setIntegral_congr_fun measurableSet_Icc fun t ht => ?_
  have ht0 : 0 < t := lt_of_lt_of_le hε₁ ht.1
  unfold heatHessianConv
  rw [← integral_sub (integrable_heatHessianConv_mul ht0 i j hf x)
    (integrable_heatHessianConv_mul ht0 i j hg x)]
  congr 1
  funext y
  simp only [Pi.sub_apply]
  ring

/-- The crude `L²` bound of the time-truncated heat Hessian. -/
theorem eLpNorm_heatHessianWindow_le_crude {ε₁ ε₂ : ℝ} (hε₁ : 0 < ε₁) (hε : ε₁ ≤ ε₂)
    (i j : Fin d) {f : Vec d → ℝ} (hfm : Measurable f) (hf : MemLp f 2 volume) :
    eLpNorm (heatHessianWindow ε₁ ε₂ i j f) 2 volume ≤
      ENNReal.ofReal ((ε₂ - ε₁) * windowHessianConst d ε₁ ε₂) * eLpNorm f 2 volume := by
  have hε₂ : 0 < 2 * ε₂ := by linarith
  set B : Vec d → ℝ := fun x => ∫ y, euclideanHeatKernel (2 * ε₂) (x - y) * |f y| with hB
  have hpt : ∀ x, |heatHessianWindow ε₁ ε₂ i j f x| ≤
      (ε₂ - ε₁) * windowHessianConst d ε₁ ε₂ * B x := by
    intro x
    unfold heatHessianWindow
    have hb := norm_setIntegral_le_of_norm_le_const (s := Icc ε₁ ε₂)
      (f := fun t => heatHessianConv t i j f x)
      (C := windowHessianConst d ε₁ ε₂ * B x) (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)
      (fun t ht => by rw [Real.norm_eq_abs]; exact abs_heatHessianConv_le_window hε₁ ht i j hf x)
    simp only [measureReal_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ ε₂ - ε₁)] at hb
    rw [← Real.norm_eq_abs]
    calc _ ≤ windowHessianConst d ε₁ ε₂ * B x * (ε₂ - ε₁) := hb
      _ = _ := by ring
  have hBl := eLpNorm_kernel_le (measurable_euclideanHeatKernel (d := d) (2 * ε₂))
    (continuous_abs.measurable.comp hfm)
  rw [lintegral_enorm_euclideanHeatKernel hε₂, one_mul] at hBl
  have hc : 0 ≤ (ε₂ - ε₁) * windowHessianConst d ε₁ ε₂ :=
    mul_nonneg (by linarith) (windowHessianConst_nonneg hε₁ hε)
  calc eLpNorm (heatHessianWindow ε₁ ε₂ i j f) 2 volume
      ≤ eLpNorm (fun x => ((ε₂ - ε₁) * windowHessianConst d ε₁ ε₂) * B x) 2 volume := by
        refine eLpNorm_mono_real
          (stronglyMeasurable_heatHessianWindow hε₁ i j hfm).aestronglyMeasurable fun x => ?_
        rw [Real.norm_eq_abs]
        exact hpt x
    _ = ENNReal.ofReal ((ε₂ - ε₁) * windowHessianConst d ε₁ ε₂) * eLpNorm B 2 volume := by
        rw [show (fun x => ((ε₂ - ε₁) * windowHessianConst d ε₁ ε₂) * B x) =
          ((ε₂ - ε₁) * windowHessianConst d ε₁ ε₂) • B from rfl, eLpNorm_const_smul,
          Real.enorm_eq_ofReal hc]
    _ ≤ ENNReal.ofReal ((ε₂ - ε₁) * windowHessianConst d ε₁ ε₂) * eLpNorm f 2 volume := by
        gcongr
        calc eLpNorm B 2 volume ≤ eLpNorm (fun y => |f y|) 2 volume := hBl
          _ = eLpNorm f 2 volume := le_antisymm
            (eLpNorm_mono (continuous_abs.measurable.comp hfm).aestronglyMeasurable fun y => by
              rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_abs])
            (eLpNorm_mono hfm.aestronglyMeasurable fun y => by
              rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_abs])

theorem integrable_heatConv_mul {t : ℝ} (ht : 0 < t) {f : Vec d → ℝ} (hf : MemLp f 2 volume)
    (x : Vec d) : Integrable (fun y => euclideanHeatKernel t (x - y) * f y) volume :=
  integrable_kernel_mul (memLp_euclideanHeatKernel ht) hf x

theorem heatConv_sub {t : ℝ} (ht : 0 < t) {f g : Vec d → ℝ} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) (x : Vec d) :
    heatConv t (f - g) x = heatConv t f x - heatConv t g x := by
  unfold heatConv
  rw [← integral_sub (integrable_heatConv_mul ht hf x) (integrable_heatConv_mul ht hg x)]
  congr 1
  funext y
  simp only [Pi.sub_apply]
  ring

theorem eLpNorm_heatConv_sub_le {t : ℝ} (ht : 0 < t) {f g : Vec d → ℝ} (hfm : Measurable f)
    (hf : MemLp f 2 volume) (hgm : Measurable g) (hg : MemLp g 2 volume) :
    eLpNorm (fun x => heatConv t f x - heatConv t g x) 2 volume ≤ eLpNorm (f - g) 2 volume := by
  have h : (fun x => heatConv t f x - heatConv t g x) = heatConv t (f - g) :=
    funext fun x => (heatConv_sub ht hf hg x).symm
  rw [h]
  exact eLpNorm_heatConv_le ht (hfm.sub hgm)

/-- The heat semigroup converges uniformly at time zero on smooth compactly supported
functions, at the rate of the time. -/
theorem abs_heatConv_sub_le_of_smooth {ψ : Vec d → ℝ} (hψ : IsSmoothCompact ψ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ε : ℝ, 0 < ε → ∀ x, |heatConv ε ψ x - ψ x| ≤ M * ε := by
  have hψ2 : ContDiff ℝ 2 ψ := hψ.1.of_le (by norm_cast)
  have hL := continuous_coordLaplacian hψ2
  have hLc := hasCompactSupport_coordLaplacian hψ.2
  obtain ⟨M, hM⟩ := hLc.exists_bound_of_continuous hL
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  refine ⟨M, hM0, fun ε hε x => ?_⟩
  rw [heatConv_eq_heatKernelConvolution hε, heatKernelConvolution_sub_initial hψ2 hψ.2 x hε.le]
  have hbound : ∀ t ∈ Set.uIoc (0 : ℝ) ε, ‖heatKernelConvolution t (coordLaplacian ψ) x‖ ≤ M := by
    intro t ht
    have ht0 : 0 < t := by
      rw [uIoc_of_le hε.le] at ht
      exact ht.1
    rw [← heatConv_eq_heatKernelConvolution ht0, heatConv, Real.norm_eq_abs]
    calc |∫ y, euclideanHeatKernel t (x - y) * coordLaplacian ψ y|
        ≤ ∫ y, |euclideanHeatKernel t (x - y) * coordLaplacian ψ y| := abs_integral_le_integral_abs
      _ ≤ ∫ y, euclideanHeatKernel t (x - y) * M := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => abs_nonneg _)
            ((integrable_euclideanHeatKernel ht0).comp_sub_left x |>.mul_const M)
            (Filter.Eventually.of_forall fun y => ?_)
          simp only
          rw [abs_mul, abs_of_nonneg (euclideanHeatKernel_nonneg ht0.le _)]
          exact mul_le_mul_of_nonneg_left ((Real.norm_eq_abs _).symm ▸ hM y)
            (euclideanHeatKernel_nonneg ht0.le _)
      _ = M := by
          rw [integral_mul_const, integral_sub_left_eq_self (euclideanHeatKernel (d := d) t)
            (μ := volume) x, integral_euclideanHeatKernel ht0, one_mul]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [Real.norm_eq_abs, sub_zero, abs_of_pos hε] at h
  exact h

theorem lintegral_enorm_heatConv_le {t : ℝ} (ht : 0 < t) {f : Vec d → ℝ} (hfm : Measurable f) :
    ∫⁻ x, ‖heatConv t f x‖ₑ ≤ ∫⁻ y, ‖f y‖ₑ := by
  have hjoint : Measurable (Function.uncurry fun x y : Vec d =>
      ‖euclideanHeatKernel t (x - y)‖ₑ * ‖f y‖ₑ) :=
    ((measurable_euclideanHeatKernel t).comp (measurable_fst.sub measurable_snd)).enorm.mul
      (hfm.comp measurable_snd).enorm
  calc ∫⁻ x, ‖heatConv t f x‖ₑ
      ≤ ∫⁻ x, ∫⁻ y, ‖euclideanHeatKernel t (x - y)‖ₑ * ‖f y‖ₑ := by
        refine lintegral_mono fun x => (enorm_integral_le_lintegral_enorm _).trans_eq ?_
        simp_rw [enorm_mul]
    _ = ∫⁻ y, ∫⁻ x, ‖euclideanHeatKernel t (x - y)‖ₑ * ‖f y‖ₑ :=
        lintegral_lintegral_swap hjoint.aemeasurable
    _ = ∫⁻ y, ‖f y‖ₑ := by
        refine lintegral_congr fun y => ?_
        rw [lintegral_mul_const _ (show Measurable fun x : Vec d =>
            ‖euclideanHeatKernel t (x - y)‖ₑ from
              ((measurable_euclideanHeatKernel t).comp (measurable_id.sub_const y)).enorm),
          lintegral_sub_right_eq_self (fun z => ‖euclideanHeatKernel t z‖ₑ) y,
          lintegral_enorm_euclideanHeatKernel ht, one_mul]

/-- The heat semigroup is continuous at time zero on smooth compactly supported functions. -/
theorem tendsto_eLpNorm_heatConv_sub_of_smooth {ψ : Vec d → ℝ} (hψ : IsSmoothCompact ψ) :
    Tendsto (fun ε => eLpNorm (fun x => heatConv ε ψ x - ψ x) 2 volume) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M, hM0, hM⟩ := abs_heatConv_sub_le_of_smooth hψ
  have hψm := hψ.1.continuous.measurable
  set L : ℝ≥0∞ := ∫⁻ y, ‖ψ y‖ₑ with hL
  have hLfin : L ≠ ⊤ := (hψ.1.continuous.integrable_of_hasCompactSupport hψ.2).2.ne
  have hbound : ∀ ε : ℝ, 0 < ε → eLpNorm (fun x => heatConv ε ψ x - ψ x) 2 volume ≤
      (ENNReal.ofReal (M * ε) * (2 * L)) ^ (1 / 2 : ℝ) := by
    intro ε hε
    have hgm : StronglyMeasurable (fun x => heatConv ε ψ x - ψ x) :=
      (stronglyMeasurable_kernel (measurable_euclideanHeatKernel ε) hψm).sub
        hψm.stronglyMeasurable
    rw [eLpNorm_two_eq hgm.aestronglyMeasurable]
    gcongr
    calc ∫⁻ x, ‖heatConv ε ψ x - ψ x‖ₑ ^ 2
        ≤ ∫⁻ x, ENNReal.ofReal (M * ε) * (‖heatConv ε ψ x‖ₑ + ‖ψ x‖ₑ) := by
          refine lintegral_mono fun x => ?_
          rw [sq]
          gcongr
          · rw [← ofReal_norm, Real.norm_eq_abs]
            exact ENNReal.ofReal_le_ofReal (hM ε hε x)
          · exact enorm_sub_le
      _ = ENNReal.ofReal (M * ε) * ((∫⁻ x, ‖heatConv ε ψ x‖ₑ) + ∫⁻ x, ‖ψ x‖ₑ) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_add_right _ hψm.enorm]
      _ ≤ ENNReal.ofReal (M * ε) * (2 * L) := by
          gcongr
          rw [two_mul]
          exact add_le_add (lintegral_enorm_heatConv_le hε hψm) le_rfl
  have hlim : Tendsto (fun ε : ℝ => (ENNReal.ofReal (M * ε) * (2 * L)) ^ (1 / 2 : ℝ))
      (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun ε : ℝ => ENNReal.ofReal (M * ε)) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun ε : ℝ => M * ε) (𝓝[>] 0) (𝓝 0) := by
        have h := ((continuous_const_mul M).tendsto (0 : ℝ)).mono_left
          (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
        simpa using h
      simpa using ENNReal.tendsto_ofReal this
    have h2 : Tendsto (fun ε : ℝ => ENNReal.ofReal (M * ε) * (2 * L)) (𝓝[>] 0) (𝓝 0) := by
      have := ENNReal.Tendsto.mul_const (b := 2 * L) h1
        (Or.inr (ENNReal.mul_ne_top (by norm_num) hLfin))
      simpa using this
    have h3 := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h3
    exact h3.comp h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Filter.Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hbound ε hε

end EinsteinFull.Homogenization
