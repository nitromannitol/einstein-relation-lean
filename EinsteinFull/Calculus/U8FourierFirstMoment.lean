import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Distribution.Sobolev
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

open MeasureTheory ENNReal
open scoped ENNReal NNReal SchwartzMap FourierTransform

namespace EinsteinFull

/-- The reciprocal Sobolev weight is square-integrable above half the
dimension. This is the fixed factor in the Fourier Hölder estimate. -/
theorem u8_euclidean_reciprocal_sobolev_weight_memL2 {d : ℕ} {s : ℝ}
    (hs : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) < 2 * s) :
    MemLp (fun x : EuclideanSpace ℝ (Fin d) =>
      (1 + ‖x‖ ^ 2) ^ (-s / 2)) 2 volume := by
  have ht : (fun x : EuclideanSpace ℝ (Fin d) =>
      (1 + ‖x‖ ^ 2) ^ (-s / 2)).HasTemperateGrowth := by
    fun_prop
  have hm : AEStronglyMeasurable (fun x : EuclideanSpace ℝ (Fin d) =>
      (1 + ‖x‖ ^ 2) ^ (-s / 2)) volume := ht.1.continuous.aestronglyMeasurable
  rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (by norm_num) (by norm_num) hm]
  suffices h : ∫⁻ x : EuclideanSpace ℝ (Fin d),
      ENNReal.ofReal ‖(1 + ‖x‖ ^ 2) ^ (-s)‖ < ⊤ by
    norm_cast
    simp_rw [ofReal_norm] at h
    simp_rw [← enorm_pow]
    convert h
    rw [← Real.rpow_mul_natCast (by positivity)]
    simp
  apply ((integrable_rpow_neg_one_add_norm_sq hs).congr _).lintegral_lt_top
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_eq_self.mpr (by positivity)]
  congr
  ring

/-- One Fourier moment times the reciprocal weight remains square-integrable
when the weight has one extra power of decay. -/
theorem u8_euclidean_first_moment_weight_memL2 {d : ℕ} {s : ℝ}
    (hs : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) < 2 * (s - 1)) :
    MemLp (fun x : EuclideanSpace ℝ (Fin d) =>
      ‖x‖ * (1 + ‖x‖ ^ 2) ^ (-s / 2)) 2 volume := by
  have hw := u8_euclidean_reciprocal_sobolev_weight_memL2 (s := s - 1) hs
  have hc : Continuous (fun x : EuclideanSpace ℝ (Fin d) =>
      ‖x‖ * (1 + ‖x‖ ^ 2) ^ (-s / 2)) :=
    continuous_norm.mul (Function.hasTemperateGrowth_one_add_norm_sq_rpow
      (EuclideanSpace ℝ (Fin d)) (-s / 2)).1.continuous
  apply hw.mono' hc.aestronglyMeasurable
  filter_upwards with x
  have hn : ‖x‖ ≤ (1 + ‖x‖ ^ 2) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    have h := Real.sqrt_le_sqrt (show ‖x‖ ^ 2 ≤ 1 + ‖x‖ ^ 2 by linarith)
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg x)] at h
    exact h
  have hp : 0 ≤ (1 + ‖x‖ ^ 2) ^ (-s / 2) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) hp)]
  calc
    ‖x‖ * (1 + ‖x‖ ^ 2) ^ (-s / 2) ≤
        (1 + ‖x‖ ^ 2) ^ (1 / 2 : ℝ) * (1 + ‖x‖ ^ 2) ^ (-s / 2) :=
      mul_le_mul_of_nonneg_right hn hp
    _ = (1 + ‖x‖ ^ 2) ^ (-(s - 1) / 2) := by
      rw [show -(s - 1) / 2 = (1 / 2 : ℝ) + (-s / 2) by ring,
        Real.rpow_add (by positivity)]

/-- A weighted L² Fourier representative yields an L¹ representative,
with the Hölder constant given by the reciprocal weight. -/
theorem u8_euclidean_fourier_L1_of_weighted_L2 {d : ℕ} {s : ℝ}
    (hs : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) < 2 * s)
    (T : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ))
    (u : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hu : TemperedDistribution.smulLeftCLM ℂ
      (fun x => ((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ)) (𝓕 T) = u) :
    ∃ v : Lp ℂ 1 (volume : Measure (EuclideanSpace ℝ (Fin d))),
      𝓕 T = (v : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) ∧
      ‖v‖ ≤ ‖((u8_euclidean_reciprocal_sobolev_weight_memL2 hs).ofReal).toLp
        (fun x => Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-s / 2)))‖ * ‖u‖ := by
  have hw : MemLp (fun x : EuclideanSpace ℝ (Fin d) =>
      Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-s / 2))) 2 volume :=
    (u8_euclidean_reciprocal_sobolev_weight_memL2 hs).ofReal
  refine ⟨hw.toLp _ • u, ?_, Lp.norm_smul_le (hw.toLp _) u⟩
  rw [Lp.toTemperedDistribution_smul_eq]
  · rw [← hu, TemperedDistribution.smulLeftCLM_smulLeftCLM_apply (by fun_prop) (by fun_prop)]
    convert! (TemperedDistribution.smulLeftCLM_const 1 (𝓕 T)).symm using 1
    · simp
    · congr
      ext x
      rw [Pi.mul_apply]
      norm_cast
      rw [← Real.rpow_add (by positivity)]
      ring_nf
      simp
  · fun_prop

/-- The first-moment integrability threshold implies the L¹ threshold. -/
theorem u8_sobolev_weight_threshold {d : ℕ} {s : ℝ}
    (hs : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) < 2 * (s - 1)) :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) < 2 * s := by linarith

/-- The Hölder representative has an integrable first Fourier moment. -/
theorem u8_euclidean_weighted_L2_first_moment {d : ℕ} {s : ℝ}
    (hs : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) < 2 * (s - 1))
    (a u : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (ha : (a : EuclideanSpace ℝ (Fin d) → ℂ) =ᵐ[volume]
      fun x => ((1 + ‖x‖ ^ 2) ^ (-s / 2) : ℝ)) :
    Integrable (fun x => ‖x‖ * ‖(a • u :
      Lp ℂ 1 (volume : Measure (EuclideanSpace ℝ (Fin d)))) x‖) := by
  let v : Lp ℂ 1 (volume : Measure (EuclideanSpace ℝ (Fin d))) := a • u
  have hm : MemLp (fun x : EuclideanSpace ℝ (Fin d) =>
      (‖x‖ * (1 + ‖x‖ ^ 2) ^ (-s / 2)) • u x) 1 volume :=
    (u8_euclidean_first_moment_weight_memL2 hs).smul (Lp.memLp u)
  have hi : Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
      ‖(‖x‖ * (1 + ‖x‖ ^ 2) ^ (-s / 2)) • u x‖) :=
    (memLp_one_iff_integrable.mp hm).norm
  apply hi.congr
  filter_upwards [Lp.coeFn_lpSMul (r := 1) a u, ha] with x hv hx
  change ‖(‖x‖ * (1 + ‖x‖ ^ 2) ^ (-s / 2)) • u x‖ = ‖x‖ * ‖v x‖
  change v x = _ at hv
  rw [hv, Pi.smul_apply', hx, norm_smul, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  ring

/-- The first moment of the weighted Fourier representative is bounded by
Hölder's inequality with the square-integrable first-moment weight. -/
theorem u8_euclidean_weighted_L2_first_moment_bound {d : ℕ} {s : ℝ}
    (hs : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) < 2 * (s - 1))
    (a u : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (ha : (a : EuclideanSpace ℝ (Fin d) → ℂ) =ᵐ[volume]
      fun x => ((1 + ‖x‖ ^ 2) ^ (-s / 2) : ℝ)) :
    (∫ x, ‖x‖ * ‖(a • u : Lp ℂ 1 (volume : Measure (EuclideanSpace ℝ (Fin d)))) x‖) ≤
      ‖((u8_euclidean_first_moment_weight_memL2 hs).ofReal).toLp
        (fun x => Complex.ofReal (‖x‖ * (1 + ‖x‖ ^ 2) ^ (-s / 2)))‖ * ‖u‖ := by
  have hw : MemLp (fun x : EuclideanSpace ℝ (Fin d) =>
      Complex.ofReal (‖x‖ * (1 + ‖x‖ ^ 2) ^ (-s / 2))) 2 volume :=
    (u8_euclidean_first_moment_weight_memL2 hs).ofReal
  let b : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))) := hw.toLp _
  have he : (fun x => ‖x‖ * ‖(a • u :
      Lp ℂ 1 (volume : Measure (EuclideanSpace ℝ (Fin d)))) x‖) =ᵐ[volume]
      fun x => ‖(b • u : Lp ℂ 1 (volume : Measure (EuclideanSpace ℝ (Fin d)))) x‖ := by
    filter_upwards [Lp.coeFn_lpSMul (r := 1) a u, Lp.coeFn_lpSMul (r := 1) b u,
      ha, MemLp.coeFn_toLp hw] with x hav hbv hax hbx
    change b x = _ at hbx
    rw [hav, hbv, Pi.smul_apply', Pi.smul_apply', hax, hbx, norm_smul, norm_smul, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    ring
  calc
    _ = ‖(b • u : Lp ℂ 1 (volume : Measure (EuclideanSpace ℝ (Fin d))))‖ := by
      rw [L1.norm_eq_integral_norm]
      exact integral_congr_ae he
    _ ≤ ‖b‖ * ‖u‖ := Lp.norm_smul_le b u

/-- Fourier L¹ control and the first moment are obtained from the same
weighted L² representative. -/
theorem u8_euclidean_fourier_L1_with_first_moment {d : ℕ} {s : ℝ}
    (hs : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) < 2 * (s - 1)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (T : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ))
      (u : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))),
      TemperedDistribution.smulLeftCLM ℂ
        (fun x => ((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ)) (𝓕 T) = u →
      ∃ v : Lp ℂ 1 (volume : Measure (EuclideanSpace ℝ (Fin d))),
        𝓕 T = (v : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) ∧
        ‖v‖ ≤ K * ‖u‖ ∧ Integrable (fun x => ‖x‖ * ‖v x‖) := by
  have hs0 := u8_sobolev_weight_threshold hs
  have hw : MemLp (fun x : EuclideanSpace ℝ (Fin d) =>
      Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-s / 2))) 2 volume :=
    (u8_euclidean_reciprocal_sobolev_weight_memL2 hs0).ofReal
  let a : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))) := hw.toLp _
  refine ⟨‖a‖, norm_nonneg _, ?_⟩
  intro T u hu
  refine ⟨a • u, ?_, Lp.norm_smul_le a u, ?_⟩
  · rw [Lp.toTemperedDistribution_smul_eq]
    · rw [← hu, TemperedDistribution.smulLeftCLM_smulLeftCLM_apply (by fun_prop) (by fun_prop)]
      convert! (TemperedDistribution.smulLeftCLM_const 1 (𝓕 T)).symm using 1
      · simp
      · congr
        ext x
        rw [Pi.mul_apply]
        norm_cast
        rw [← Real.rpow_add (by positivity)]
        ring_nf
        simp
    · fun_prop
  · apply u8_euclidean_weighted_L2_first_moment hs a u
    exact MemLp.coeFn_toLp hw

/-- One Fourier representative satisfies both the L¹ and first-moment
bounds needed for quantitative C¹ estimates. -/
theorem u8_euclidean_fourier_L1_quantitative {d : ℕ} {s : ℝ}
    (hs : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) < 2 * (s - 1)) :
    ∃ K M : ℝ, 0 ≤ K ∧ 0 ≤ M ∧
      ∀ (T : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ))
        (u : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))),
      TemperedDistribution.smulLeftCLM ℂ
        (fun x => ((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ)) (𝓕 T) = u →
      ∃ v : Lp ℂ 1 (volume : Measure (EuclideanSpace ℝ (Fin d))),
        𝓕 T = (v : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) ∧
        ‖v‖ ≤ K * ‖u‖ ∧ Integrable (fun x => ‖x‖ * ‖v x‖) ∧
        (∫ x, ‖x‖ * ‖v x‖) ≤ M * ‖u‖ := by
  have hs0 := u8_sobolev_weight_threshold hs
  have hw : MemLp (fun x : EuclideanSpace ℝ (Fin d) =>
      Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-s / 2))) 2 volume :=
    (u8_euclidean_reciprocal_sobolev_weight_memL2 hs0).ofReal
  let a : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))) := hw.toLp _
  let b : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
    ((u8_euclidean_first_moment_weight_memL2 hs).ofReal).toLp _
  refine ⟨‖a‖, ‖b‖, norm_nonneg _, norm_nonneg _, ?_⟩
  intro T u hu
  refine ⟨a • u, ?_, Lp.norm_smul_le a u, ?_, ?_⟩
  · rw [Lp.toTemperedDistribution_smul_eq]
    · rw [← hu, TemperedDistribution.smulLeftCLM_smulLeftCLM_apply (by fun_prop) (by fun_prop)]
      convert! (TemperedDistribution.smulLeftCLM_const 1 (𝓕 T)).symm using 1
      · simp
      · congr
        ext x
        rw [Pi.mul_apply]
        norm_cast
        rw [← Real.rpow_add (by positivity)]
        ring_nf
        simp
    · fun_prop
  · exact u8_euclidean_weighted_L2_first_moment hs a u (MemLp.coeFn_toLp hw)
  · exact u8_euclidean_weighted_L2_first_moment_bound hs a u (MemLp.coeFn_toLp hw)

/-- An integrable first Fourier moment gives a bounded C¹ inverse transform. -/
theorem u8_euclidean_inverse_fourier_C1 {d : ℕ}
    (v : Lp ℂ 1 (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (h : Integrable (fun x => ‖x‖ * ‖v x‖)) :
    ContDiff ℝ 1 (Real.Lp.fourierTransformInv v) := by
  have hm : ∀ n : ℕ, n ≤ (1 : ℕ∞) →
      Integrable (fun x : EuclideanSpace ℝ (Fin d) => ‖x‖ ^ n * ‖v x‖) := by
    intro n hn
    have hn' : n ≤ 1 := by exact_mod_cast hn
    interval_cases n
    · simpa using (L1.integrable_coeFn v).norm
    · simpa using h
  have hd : ContDiff ℝ 1 (𝓕 (v : EuclideanSpace ℝ (Fin d) → ℂ)) :=
    Real.contDiff_fourier hm
  rw [Real.Lp.coe_fourierTransformInv]
  have hi : 𝓕⁻ (v : EuclideanSpace ℝ (Fin d) → ℂ) =
      (fun x => 𝓕 (v : EuclideanSpace ℝ (Fin d) → ℂ) (-x)) := by
    funext x
    exact Real.fourierInv_eq_fourier_neg _ x
  rw [hi]
  exact hd.comp contDiff_id.neg

open scoped RealInnerProductSpace

/-- The derivative of the inverse Fourier transform is bounded by its first moment. -/
theorem u8_euclidean_inverse_fourier_derivative_bound {d : ℕ}
    (v : Lp ℂ 1 (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (h : Integrable (fun ξ => ‖ξ‖ * ‖v ξ‖))
    (x : EuclideanSpace ℝ (Fin d)) :
    ‖fderiv ℝ (fun z => Real.Lp.fourierTransformInv v z) x‖ ≤
      2 * Real.pi * ∫ ξ, ‖ξ‖ * ‖v ξ‖ := by
  let L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ :=
    -innerSL ℝ
  have hd := VectorFourier.hasFDerivAt_fourierIntegral L (L1.integrable_coeFn v) h x
  have he : (fun z => Real.Lp.fourierTransformInv v z) =
      VectorFourier.fourierIntegral Real.fourierChar volume L.toLinearMap₁₂ v := by
    rw [Real.Lp.coe_fourierTransformInv]
    rfl
  rw [he, hd.fderiv]
  calc
    _ ≤ ∫ ξ, ‖VectorFourier.fourierSMulRight L (fun ξ => v ξ) ξ‖ :=
      VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
    _ ≤ ∫ ξ, (2 * Real.pi) * (‖ξ‖ * ‖v ξ‖) := by
      apply integral_mono_of_nonneg
      · exact ae_of_all _ (fun _ => norm_nonneg _)
      · exact h.const_mul _
      · filter_upwards with ξ
        rw [VectorFourier.norm_fourierSMulRight]
        have hn : ‖L ξ‖ = ‖ξ‖ := by
          simpa only [L, neg_apply, norm_neg] using
            (innerSL_apply_norm (𝕜 := ℝ) ξ)
        rw [hn]
        ring_nf
        exact le_rfl
    _ = _ := integral_const_mul _ _

/-- An L¹ Fourier representative inverts to the original L² class
almost everywhere. -/
theorem u8_euclidean_inverse_fourier_ae {d : ℕ}
    (u : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (v : Lp ℂ 1 (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hv : 𝓕 (u : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) =
      (v : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ))) :
    (Real.Lp.fourierTransformInv v : EuclideanSpace ℝ (Fin d) → ℂ) =ᵐ[volume] u := by
  apply ae_eq_of_integral_contDiff_smul_eq
    (Real.Lp.fourierTransformInv v).continuous.locallyIntegrable
    ((Lp.memLp u).locallyIntegrable (by norm_num))
  intro g hg hgc
  have hgc' : HasCompactSupport (Complex.ofRealCLM ∘ g) := hgc.comp_left rfl
  let φ : 𝓢(EuclideanSpace ℝ (Fin d), ℂ) :=
    hgc'.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hg)
  have hh := congrArg (fun T : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ) => T (𝓕⁻ φ)) hv
  simp only [TemperedDistribution.fourier_apply, FourierTransform.fourier_fourierInv_eq,
    Lp.toTemperedDistribution_apply, smul_eq_mul] at hh
  have hswap := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (L := -innerₗ (EuclideanSpace ℝ (Fin d))) (μ := volume) (ν := volume)
    Real.continuous_fourierChar
    continuous_inner.neg
    (L1.integrable_coeFn v) φ.integrable
  have hi : (∫ x, (𝓕⁻ (v : EuclideanSpace ℝ (Fin d) → ℂ)) x * φ x) =
      ∫ x, v x * (𝓕⁻ φ) x := by
    simpa [SchwartzMap.fourierInv_coe, Real.fourierInv_eq,
      VectorFourier.fourierIntegral, real_inner_comm, smul_eq_mul] using hswap
  have hh' : (∫ x, v x * (𝓕⁻ φ) x) = ∫ x, u x * φ x := by
    simpa only [mul_comm] using hh.symm
  rw [Real.Lp.coe_fourierTransformInv]
  simpa [φ, mul_comm, smul_eq_mul] using hi.trans hh'

/-- The inverse Fourier transform of an L¹ class has supremum norm at most
its L¹ norm. -/
theorem u8_euclidean_inverse_fourier_norm_le {d : ℕ}
    (v : Lp ℂ 1 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    ‖Real.Lp.fourierTransformInv v‖ ≤ ‖v‖ := by
  rw [BoundedContinuousFunction.norm_le (norm_nonneg v)]
  intro x
  rw [Real.Lp.fourierTransformInv_apply, Real.fourierInv_eq_fourier_neg,
    Real.fourier_eq]
  apply (norm_integral_le_integral_norm _).trans
  simp_rw [Circle.norm_smul]
  exact (L1.norm_eq_integral_norm v).symm.le


/-- An integrable Fourier density with integrable first moment has a C¹ inverse transform. -/
theorem u8_fourier_first_moment_C1_consumer
    {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → ℂ)
    (hF : Integrable F) (hF1 : Integrable (fun ξ => ‖ξ‖ * ‖F ξ‖)) :
    ContDiff ℝ 1 (fun x : EuclideanSpace ℝ (Fin d) =>
      ∫ ξ, Complex.exp (2 * Real.pi * Complex.I * (inner ℝ ξ x : ℂ)) * F ξ) := by
  have hm : ∀ n : ℕ, n ≤ (1 : ℕ∞) →
      Integrable (fun x : EuclideanSpace ℝ (Fin d) => ‖x‖ ^ n * ‖F x‖) := by
    intro n hn
    have hn' : n ≤ 1 := by exact_mod_cast hn
    interval_cases n
    · simpa using hF.norm
    · simpa using hF1
  have hd : ContDiff ℝ 1 (𝓕 F) := Real.contDiff_fourier hm
  have hi : ContDiff ℝ 1 (𝓕⁻ F) := by
    rw [show 𝓕⁻ F = (fun x => 𝓕 F (-x)) from funext (Real.fourierInv_eq_fourier_neg F)]
    exact hd.comp contDiff_id.neg
  convert hi using 1
  funext x
  rw [Real.fourierInv_eq']
  apply integral_congr_ae
  filter_upwards with ξ
  simp only [smul_eq_mul]
  congr 1
  push_cast
  ring

open scoped RealInnerProductSpace

/-- The derivative of the inverse transform is bounded by the first moment. -/
theorem u8_fourier_first_moment_derivative_bound
    {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → ℂ)
    (hF : Integrable F) (hF1 : Integrable (fun ξ => ‖ξ‖ * ‖F ξ‖))
    (x : EuclideanSpace ℝ (Fin d)) :
    ‖fderiv ℝ (fun x : EuclideanSpace ℝ (Fin d) =>
      ∫ ξ, Complex.exp (2 * Real.pi * Complex.I * (inner ℝ ξ x : ℂ)) * F ξ) x‖ ≤
      2 * Real.pi * ∫ ξ, ‖ξ‖ * ‖F ξ‖ := by
  let L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ :=
    -innerSL ℝ
  have hd := VectorFourier.hasFDerivAt_fourierIntegral L hF hF1 x
  have he : (fun x : EuclideanSpace ℝ (Fin d) =>
      ∫ ξ, Complex.exp (2 * Real.pi * Complex.I * (inner ℝ ξ x : ℂ)) * F ξ) =
      VectorFourier.fourierIntegral Real.fourierChar volume L.toLinearMap₁₂ F := by
    funext x
    change (∫ ξ, Complex.exp (2 * Real.pi * Complex.I * (inner ℝ ξ x : ℂ)) * F ξ) =
      (𝓕⁻ F) x
    rw [Real.fourierInv_eq']
    apply integral_congr_ae
    filter_upwards with ξ
    simp only [smul_eq_mul]
    congr 1
    push_cast
    ring
  rw [he, hd.fderiv]
  calc
    _ ≤ ∫ ξ, ‖VectorFourier.fourierSMulRight L F ξ‖ :=
      VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
    _ ≤ ∫ ξ, (2 * Real.pi) * (‖ξ‖ * ‖F ξ‖) := by
      apply integral_mono_of_nonneg
      · exact ae_of_all _ (fun _ => norm_nonneg _)
      · exact hF1.const_mul _
      · filter_upwards with ξ
        rw [VectorFourier.norm_fourierSMulRight]
        have hn : ‖L ξ‖ = ‖ξ‖ := by
          simpa only [L, neg_apply, norm_neg] using
            (innerSL_apply_norm (𝕜 := ℝ) ξ)
        rw [hn]
        ring_nf
        exact le_rfl
    _ = _ := integral_const_mul _ _

/-- Every directional derivative is controlled by the Euclidean length of its direction. -/
theorem u8_fourier_first_moment_directional_bound
    {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → ℂ)
    (hF : Integrable F) (hF1 : Integrable (fun ξ => ‖ξ‖ * ‖F ξ‖))
    (x y : EuclideanSpace ℝ (Fin d)) :
    ‖fderiv ℝ (fun x : EuclideanSpace ℝ (Fin d) =>
      ∫ ξ, Complex.exp (2 * Real.pi * Complex.I * (inner ℝ ξ x : ℂ)) * F ξ) x y‖ ≤
      (2 * Real.pi * ∫ ξ, ‖ξ‖ * ‖F ξ‖) * ‖y‖ := by
  exact ((fderiv ℝ (fun x : EuclideanSpace ℝ (Fin d) =>
    ∫ ξ, Complex.exp (2 * Real.pi * Complex.I * (inner ℝ ξ x : ℂ)) * F ξ) x).le_opNorm y).trans
      (mul_le_mul_of_nonneg_right
        (u8_fourier_first_moment_derivative_bound F hF hF1 x) (norm_nonneg y))

end EinsteinFull
