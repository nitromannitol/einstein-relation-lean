import EinsteinFull.Homogenization.HeatGradientWindow
import EinsteinFull.Homogenization.KernelConvolutionHessian

/-!
# The weak gradient of the time-truncated heat gradient

For a function `f` with Gaussian moments, the time-truncated heat gradient
`∫_{ε₁}^{ε₂} ∂ⱼΦ_t * f dt` has the time-truncated heat Hessian `∫_{ε₁}^{ε₂} ∂ₗ∂ⱼΦ_t * f dt` as its
weak `ℓ`-th derivative. The proof tests against a smooth compactly supported function, exchanges
the integrals by Fubini's theorem and integrates by parts against the smooth kernel. This is the
potential of the truncations of the heat formula (6.7) in Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace EinsteinFull.Homogenization

open EinsteinRelation EinsteinRelation.Correctors EinsteinRelation.External.AKM

variable {d : ℕ}

theorem exists_euclideanNorm_le_of_hasCompactSupport {φ : Vec d → ℝ} (hφ : HasCompactSupport φ) :
    ∃ ρ : ℝ, ∀ x ∈ tsupport φ, euclideanNorm x ≤ ρ := by
  obtain ⟨ρ, hρ⟩ := hφ.isCompact.exists_bound_of_continuousOn
    (continuous_euclideanNorm (d := d)).continuousOn
  exact ⟨ρ, fun x hx => (le_abs_self _).trans ((Real.norm_eq_abs _) ▸ hρ x hx)⟩

theorem isOpen_ball_zero (R : ℝ) : IsOpen (ball (0 : Vec d) R) :=
  isOpen_lt (continuous_euclideanNorm.comp (continuous_id.sub continuous_const)) continuous_const

/-- Square integrability on every centered ball gives local integrability. -/
theorem locallyIntegrable_of_memLp_ball {u : Vec d → ℝ}
    (hu : ∀ R : ℝ, MemLp u 2 (volume.restrict (ball 0 R))) : LocallyIntegrable u volume := by
  intro x
  refine ⟨ball 0 (euclideanNorm x + 1), (isOpen_ball_zero _).mem_nhds ?_, ?_⟩
  · change euclideanNorm (x - 0) < euclideanNorm x + 1
    rw [sub_zero]
    linarith
  · have hfin : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) (euclideanNorm x + 1))) :=
      isFiniteMeasure_restrict.mpr (volume_ball_zero_lt_top _).ne
    exact (hu _).integrable (by norm_num)

/-- **Fubini for a dominated kernel**: testing a kernel convolution against a compactly supported
continuous function. -/
theorem integral_kernelConv_mul_eq {K f φ : Vec d → ℝ} (hK : Measurable K) (hfm : Measurable f)
    (hf : HasGaussianMoments f) {s c : ℝ} (hs : 0 < s)
    (hKb : ∀ z, |K z| ≤ c * euclideanHeatKernel s z) (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) :
    ∫ x, (∫ y, K (x - y) * f y) * φ x = ∫ y, f y * ∫ x, K (x - y) * φ x := by
  obtain ⟨ρ, hρ⟩ := exists_euclideanNorm_le_of_hasCompactSupport hφc
  obtain ⟨B, hB⟩ := hf s hs ρ
  have hc : 0 ≤ c := by
    have h := (abs_nonneg (K 0)).trans (hKb 0)
    by_contra hneg
    have hpos : 0 < euclideanHeatKernel s (0 : Vec d) := by
      unfold euclideanHeatKernel
      positivity
    nlinarith
  have hmeas : AEStronglyMeasurable (Function.uncurry fun x y : Vec d => K (x - y) * f y * φ x)
      (volume.prod volume) :=
    (((hK.comp (measurable_fst.sub measurable_snd)).mul (hfm.comp measurable_snd)).mul
      (hφ.measurable.comp measurable_fst)).aestronglyMeasurable
  have hint : Integrable (Function.uncurry fun x y : Vec d => K (x - y) * f y * φ x)
      (volume.prod volume) := by
    rw [integrable_prod_iff hmeas]
    have hφint : Integrable φ volume := hφ.integrable_of_hasCompactSupport hφc
    obtain ⟨Mφ, hMφ⟩ := hφc.exists_bound_of_continuous hφ
    refine ⟨Filter.Eventually.of_forall fun x => ?_, ?_⟩
    · by_cases hx : x ∈ tsupport φ
      · have hix := (hB x (hρ x hx)).1
        refine ((hix.const_mul c).mul_const |φ x|).mono'
          (((hK.comp (measurable_const.sub measurable_id)).mul hfm).mul_const
            (φ x)).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
        simp only [Function.uncurry_apply_pair, Real.norm_eq_abs, abs_mul]
        have h1 := hKb (x - y)
        have h2 : 0 ≤ |f y| := abs_nonneg _
        have h3 : 0 ≤ |φ x| := abs_nonneg _
        calc |K (x - y)| * |f y| * |φ x| ≤ c * euclideanHeatKernel s (x - y) * |f y| * |φ x| := by
              gcongr
          _ = c * (euclideanHeatKernel s (x - y) * |f y|) * |φ x| := by ring
      · have h0 : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
        simp [Function.uncurry_apply_pair, h0]
    · refine (hφint.norm.const_mul (c * max B 0)).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
      · exact (hmeas.norm.integral_prod_right' (μ := volume) (ν := volume))
      · simp only [Function.uncurry_apply_pair]
        by_cases hx : x ∈ tsupport φ
        · rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
          calc ∫ y, ‖K (x - y) * f y * φ x‖
              ≤ ∫ y, c * (euclideanHeatKernel s (x - y) * |f y|) * ‖φ x‖ := by
                refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
                  (((hB x (hρ x hx)).1.const_mul c).mul_const _)
                  (Filter.Eventually.of_forall fun y => ?_)
                simp only [norm_mul, Real.norm_eq_abs]
                rw [← mul_assoc c]
                gcongr
                exact hKb _
            _ = c * (∫ y, euclideanHeatKernel s (x - y) * |f y|) * ‖φ x‖ := by
                rw [integral_mul_const, integral_const_mul]
            _ ≤ c * max B 0 * ‖φ x‖ := by
                gcongr
                exact (hB x (hρ x hx)).2.trans (le_max_left _ _)
        · have h0 : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
          simp [h0]
  have hswap := integral_integral_swap hint
  calc ∫ x, (∫ y, K (x - y) * f y) * φ x = ∫ x, ∫ y, K (x - y) * f y * φ x := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only
        rw [integral_mul_const]
    _ = ∫ y, ∫ x, K (x - y) * f y * φ x := hswap
    _ = ∫ y, f y * ∫ x, K (x - y) * φ x := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only
        rw [← integral_const_mul]
        congr 1
        funext x
        ring

/-- Integration by parts against a translated heat-kernel gradient. -/
theorem integral_heatGrad_sub_mul_coordinateDerivative {t : ℝ} (j l : Fin d) (y : Vec d)
    {ψ : Vec d → ℝ} (hψ : IsSmoothCompact ψ) :
    ∫ x, coordinateDerivative j (euclideanHeatKernel t) (x - y) * coordinateDerivative l ψ x =
      -∫ x, coordinateDerivative l (coordinateDerivative j (euclideanHeatKernel t)) (x - y) *
        ψ x := by
  set F : Vec d → ℝ := fun x => coordinateDerivative j (euclideanHeatKernel t) (x - y) with hF
  have hFs : ContDiff ℝ (⊤ : ℕ∞) F :=
    (contDiff_coordinateDerivative (contDiff_euclideanHeatKernel t) j).comp
      (contDiff_id.sub contDiff_const)
  have hdF : ∀ x, fderiv ℝ F x (unitVector l) =
      coordinateDerivative l (coordinateDerivative j (euclideanHeatKernel t)) (x - y) := by
    intro x
    rw [hF, fderiv_comp_sub]
    rfl
  have hFd : Differentiable ℝ F := hFs.differentiable (by simp)
  have hψd : Differentiable ℝ ψ := hψ.1.differentiable (by simp)
  have hlψ := hψ.coordinateDerivative l
  have hcont : Continuous (fun x =>
      coordinateDerivative l (coordinateDerivative j (euclideanHeatKernel t)) (x - y)) :=
    (contDiff_coordinateDerivative (contDiff_coordinateDerivative
      (contDiff_euclideanHeatKernel t) j) l).continuous.comp (continuous_id.sub continuous_const)
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := F) (g := ψ) (v := unitVector l)
    (by simpa only [hdF] using integrable_mul_of_hasCompactSupport_right hcont hψ.1.continuous hψ.2)
    (integrable_mul_of_hasCompactSupport_right hFs.continuous hlψ.1.continuous hlψ.2)
    (integrable_mul_of_hasCompactSupport_right hFs.continuous hψ.1.continuous hψ.2)
    (fun x _ => hFd x) (fun x _ => hψd x)
  simp only [hdF] at h
  exact h

/-- The weak derivative identity of the heat gradient at one time. -/
theorem HasGaussianMoments.integral_heatGradConv_mul {f : Vec d → ℝ} (hf : HasGaussianMoments f)
    (hfm : Measurable f) {t : ℝ} (ht : 0 < t) (j l : Fin d) {ψ : Vec d → ℝ}
    (hψ : IsSmoothCompact ψ) :
    ∫ x, heatGradConv t j f x * coordinateDerivative l ψ x =
      -∫ x, heatHessianConv t j l f x * ψ x := by
  have hlψ := hψ.coordinateDerivative l
  have h1 := integral_kernelConv_mul_eq (measurable_heatGrad t j) hfm hf (s := 2 * t)
    (c := (2 : ℝ) ^ ((d : ℝ) / 2) * (2 / Real.sqrt t)) (by positivity) (abs_heatGrad_le ht j)
    hlψ.1.continuous hlψ.2
  have h2 := integral_kernelConv_mul_eq (measurable_heatHessian ht j l) hfm hf (s := 2 * t)
    (c := (2 : ℝ) ^ ((d : ℝ) / 2) * (2 / t)) (by positivity) (abs_heatHessian_le ht j l)
    hψ.1.continuous hψ.2
  unfold heatGradConv heatHessianConv
  rw [h1, h2, ← integral_neg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only
  rw [integral_heatGrad_sub_mul_coordinateDerivative j l y hψ]
  ring

/-- **Fubini in time** for families bounded on the support of the test function. -/
theorem integral_setIntegral_mul_swap {A : ℝ → Vec d → ℝ} {a b : ℝ}
    (hA : AEStronglyMeasurable (fun p : Vec d × ℝ => A p.2 p.1)
      (volume.prod (volume.restrict (Icc a b)))) {φ : Vec d → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) {C : ℝ}
    (hC : ∀ t ∈ Icc a b, ∀ x ∈ tsupport φ, |A t x| ≤ C) :
    ∫ x, (∫ t in Icc a b, A t x) * φ x = ∫ t in Icc a b, ∫ x, A t x * φ x := by
  have hfin := isFiniteMeasure_restrict_Icc a b
  have hprod : (volume : Measure (Vec d)).prod (volume.restrict (Icc a b)) =
      ((volume : Measure (Vec d)).prod (volume : Measure ℝ)).restrict (univ ×ˢ Icc a b) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hφint : Integrable φ volume := hφ.integrable_of_hasCompactSupport hφc
  have hint : Integrable (Function.uncurry fun (x : Vec d) (t : ℝ) => A t x * φ x)
      ((volume : Measure (Vec d)).prod (volume.restrict (Icc a b))) := by
    refine (hφint.abs.mul_prod (integrable_const C)).mono'
      (hA.mul (hφ.measurable.comp measurable_fst).aestronglyMeasurable) ?_
    rw [hprod]
    filter_upwards [ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Icc)] with p hp
    simp only [Function.uncurry, Real.norm_eq_abs, abs_mul]
    by_cases hx : p.1 ∈ tsupport φ
    · rw [mul_comm |φ p.1| C]
      exact mul_le_mul_of_nonneg_right (hC p.2 hp.2 p.1 hx) (abs_nonneg _)
    · rw [image_eq_zero_of_notMem_tsupport hx, abs_zero, mul_zero, zero_mul]
  rw [← integral_integral_swap hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [integral_mul_const]

/-- **The weak gradient of the time-truncated heat gradient** is the time-truncated heat
Hessian. -/
theorem HasGaussianMoments.hasWeakPartialDerivative_heatGradWindow {f : Vec d → ℝ}
    (hf : HasGaussianMoments f) (hfm : Measurable f) {ε₁ ε₂ : ℝ} (hε₁ : 0 < ε₁)
    (hε : ε₁ ≤ ε₂) (j l : Fin d) :
    HasWeakPartialDerivative univ l (heatGradWindow ε₁ ε₂ j f)
      (heatHessianWindow ε₁ ε₂ j l f) := by
  refine ⟨locallyIntegrableOn_univ.mpr (locallyIntegrable_of_memLp_ball fun R =>
      hf.memLp_heatGradWindow hε₁ hε j hfm R),
    locallyIntegrableOn_univ.mpr (locallyIntegrable_of_memLp_ball fun R =>
      hf.memLp_heatHessianWindow hε₁ hε j l hfm R), fun ψ hψt => ?_⟩
  have hψ : IsSmoothCompact ψ := ⟨hψt.1, hψt.2.1⟩
  have hlψ := hψ.coordinateDerivative l
  rw [Measure.restrict_univ]
  obtain ⟨ρ, hρ⟩ := exists_euclideanNorm_le_of_hasCompactSupport hψ.2
  obtain ⟨B, hB⟩ := hf (2 * ε₂) (by linarith) ρ
  have hprod : (volume : Measure (Vec d)).prod (volume.restrict (Icc ε₁ ε₂)) =
      ((volume : Measure (Vec d)).prod (volume : Measure ℝ)).restrict (univ ×ˢ Icc ε₁ ε₂) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hgradm : AEStronglyMeasurable (fun p : Vec d × ℝ => heatGradConv p.2 j f p.1)
      ((volume : Measure (Vec d)).prod (volume.restrict (Icc ε₁ ε₂))) := by
    refine ((stronglyMeasurable_heatGradKernelConv j hfm).comp_measurable
      measurable_swap).aestronglyMeasurable.congr (Filter.Eventually.of_forall fun p => ?_)
    exact (heatGradConv_eq_kernel p.2 j f p.1).symm
  have hhessm : AEStronglyMeasurable (fun p : Vec d × ℝ => heatHessianConv p.2 j l f p.1)
      ((volume : Measure (Vec d)).prod (volume.restrict (Icc ε₁ ε₂))) := by
    refine ((stronglyMeasurable_heatHessianKernelConv j l hfm).comp_measurable
      measurable_swap).aestronglyMeasurable.congr ?_
    rw [hprod]
    filter_upwards [ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Icc)] with p hp
    exact (heatHessianConv_eq_kernel (lt_of_lt_of_le hε₁ hp.2.1) j l f p.1).symm
  have hgrad := integral_setIntegral_mul_swap hgradm hlψ.1.continuous hlψ.2
    (C := windowGradConst d ε₁ ε₂ * B) fun t ht x hx =>
      abs_heatGradConv_le_of_bound hε₁ ht j hB (hρ x (tsupport_fderiv_apply_subset ℝ _ hx))
  have hhess := integral_setIntegral_mul_swap hhessm hψ.1.continuous hψ.2
    (C := windowHessianConst d ε₁ ε₂ * B) fun t ht x hx =>
      abs_heatHessianConv_le_of_bound hε₁ ht j l hB (hρ x hx)
  unfold heatGradWindow heatHessianWindow
  rw [hgrad, hhess, ← integral_neg]
  exact setIntegral_congr_fun measurableSet_Icc fun t ht =>
    hf.integral_heatGradConv_mul hfm (lt_of_lt_of_le hε₁ ht.1) j l hψ

end EinsteinFull.Homogenization
