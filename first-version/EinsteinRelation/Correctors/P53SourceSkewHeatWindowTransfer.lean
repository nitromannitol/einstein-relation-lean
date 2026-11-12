import EinsteinRelation.Correctors.IntegratedHeatTransfer
import EinsteinRelation.Correctors.HeatTransferMoments
import EinsteinRelation.Correctors.HeatTransferTimeIntegrability
import EinsteinRelation.Correctors.HeatGradientUniformLp
import EinsteinRelation.Correctors.HeatSmoothingContraction
import EinsteinRelation.Correctors.P53SourceSkewHeatKernelBounds
import EinsteinRelation.Correctors.P53SourceSkewTruncationPairing

/-!
# Heat transfer on positive time windows

Source: `paper/main.tex:732-748`; AKM Lemma 6.1, Step 4. The time integral of the
heat-smoothed source tested against `ΔK` over `[a, b]` is the difference of the
endpoint heat averages tested against `K`. The small-time endpoint converges in
`L¹` to the unsmoothed average, and translating the test changes the large-time
endpoint by an `L¹`-small amount.
-/

open MeasureTheory Filter Topology
namespace EinsteinRelation.Correctors

/-- The heat-transfer identity on a positive window. Source: AKM Lemma 6.1, Step 4. -/
theorem ae_setIntegral_horizontalMollify_laplacian_heatSmoothed {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {K : Vec d → ℝ} (hK : ContDiff ℝ 2 K) (hKc : HasCompactSupport K)
    {f : FieldPair d → ℝ} (hf : Measurable f) (hfi : Integrable f Q)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∀ᵐ ω ∂Q, IntegrableOn
        (fun t => horizontalMollify (coordLaplacian K) (heatSmoothed t f) ω) (Set.Icc a b) ∧
      (∫ t in Set.Icc a b, horizontalMollify (coordLaplacian K) (heatSmoothed t f) ω) =
        horizontalMollify K (heatSmoothed b f) ω - horizontalMollify K (heatSmoothed a f) ω := by
  have hb : 0 ≤ b := ha.trans hab
  have hL : Measurable (coordLaplacian K) := (continuous_coordLaplacian hK).measurable
  have hLi : Integrable (coordLaplacian K) := integrable_coordLaplacian hK hKc
  filter_upwards [horizontalMollify_heat_transfer Q hQ hK hKc hf hfi ha,
    horizontalMollify_heat_transfer Q hQ hK hKc hf hfi hb,
    ae_intervalIntegrable_horizontalMollify_heatSmoothed Q hQ hL hLi hf hfi hb]
    with ω hTa hTb hint
  have hsub : Set.uIcc 0 a ⊆ Set.uIcc 0 b := by
    rw [Set.uIcc_of_le ha, Set.uIcc_of_le hb]
    exact Set.Icc_subset_Icc le_rfl hab
  have hint0a := hint.mono_set hsub
  have hintab : IntervalIntegrable (fun t => horizontalMollify (coordLaplacian K)
      (heatSmoothed t f) ω) volume a b := by
    refine hint.mono_set ?_
    rw [Set.uIcc_of_le hab, Set.uIcc_of_le hb]
    exact Set.Icc_subset_Icc ha le_rfl
  have hOn : IntegrableOn (fun t => horizontalMollify (coordLaplacian K)
      (heatSmoothed t f) ω) (Set.Icc a b) :=
    (integrableOn_Icc_iff_integrableOn_Ioc (μ := volume)).mpr
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hintab)
  refine ⟨hOn, ?_⟩
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    ← intervalIntegral.integral_interval_sub_left hint hint0a]
  unfold heatTransferExpression at hTa hTb
  linarith

/-- Small-time endpoint: `hM K (H_a f) → hM K f` in `L¹` along `a = (m+1)⁻¹`. -/
theorem tendsto_eLpNorm_horizontalMollify_heatSmoothed_inv_sub {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {K : Vec d → ℝ} (hK : ContDiff ℝ 2 K) (hKc : HasCompactSupport K)
    {f : FieldPair d → ℝ} (hf : Measurable f) (hfi : Integrable f Q) :
    Tendsto (fun m : ℕ => eLpNorm (fun ω =>
      horizontalMollify K (heatSmoothed (((m + 1 : ℕ) : ℝ)⁻¹) f) ω -
        horizontalMollify K f ω) 1 Q) atTop (𝓝 0) := by
  have hL : Measurable (coordLaplacian K) := (continuous_coordLaplacian hK).measurable
  have hLi : Integrable (coordLaplacian K) := integrable_coordLaplacian hK hKc
  set M : ℝ := (eLpNorm f 1 Q).toReal with hMdef
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  have hfn : ∀ t : ℝ, 0 ≤ t → eLpNorm (heatSmoothed t f) (ENNReal.ofReal 1) Q ≤
      ENNReal.ofReal (M * heatAveragingProfile 1 t) := by
    intro t ht
    refine (eLpNorm_heatSmoothed_le Q hQ le_rfl hf ht).trans ?_
    rw [ENNReal.ofReal_one,
      ← ENNReal.ofReal_toReal (memLp_one_iff_integrable.mpr hfi).eLpNorm_ne_top]
    refine ENNReal.ofReal_le_ofReal ?_
    have hp : 1 ≤ heatAveragingProfile 1 t := by
      unfold heatAveragingProfile
      have : 0 ≤ (Real.sqrt (1 + t))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
      linarith [inv_one (G := ℝ)]
    nlinarith
  have hbound (a : ℝ) (ha : 0 ≤ a) : eLpNorm (fun ω =>
      horizontalMollify K (heatSmoothed a f) ω - horizontalMollify K f ω) 1 Q ≤
      ENNReal.ofReal ((∫ x, |coordLaplacian K x|) * M * (2 * a)) := by
    have hmom := (integral_horizontalMollify_heatSmoothed_moment_le Q hQ le_rfl hM one_pos ha
      hL hLi hf hfn).2.2
    rw [ENNReal.ofReal_one] at hmom
    have heq : (fun ω => horizontalMollify K (heatSmoothed a f) ω - horizontalMollify K f ω)
        =ᵐ[Q] fun ω => ∫ t in (0 : ℝ)..a, horizontalMollify (coordLaplacian K)
          (heatSmoothed t f) ω := by
      filter_upwards [horizontalMollify_heat_transfer Q hQ hK hKc hf hfi ha] with ω hω
      unfold heatTransferExpression at hω
      linarith
    rw [eLpNorm_congr_ae heq]
    refine hmom.trans (ENNReal.ofReal_le_ofReal ?_)
    have hprof : (∫ t in (0 : ℝ)..a, heatAveragingProfile 1 t) ≤ 2 * a := by
      have hle : ∀ t ∈ Set.Icc (0 : ℝ) a, heatAveragingProfile 1 t ≤ 2 := by
        intro t ht
        unfold heatAveragingProfile
        have h1 : (Real.sqrt (1 + t))⁻¹ ≤ 1 := by
          apply inv_le_one_of_one_le₀
          rw [Real.one_le_sqrt]
          linarith [ht.1]
        linarith [inv_one (G := ℝ)]
      calc (∫ t in (0 : ℝ)..a, heatAveragingProfile 1 t) ≤ ∫ t in (0 : ℝ)..a, (2 : ℝ) :=
            intervalIntegral.integral_mono_on ha (intervalIntegrable_heatAveragingProfile 1 ha)
              intervalIntegrable_const hle
        _ = 2 * a := by simp; ring
    have hc : 0 ≤ (∫ x, |coordLaplacian K x|) * M :=
      mul_nonneg (integral_nonneg fun _ => abs_nonneg _) hM
    exact mul_le_mul_of_nonneg_left hprof hc
  have hlim : Tendsto (fun m : ℕ => ENNReal.ofReal ((∫ x, |coordLaplacian K x|) * M *
      (2 * ((m + 1 : ℕ) : ℝ)⁻¹))) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.tendsto_ofReal ?_
    have h : Tendsto (fun m : ℕ => ((m + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) := by
      simpa only [Nat.cast_add, Nat.cast_one] using tendsto_inv_atTop_zero.comp
        (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    simpa using (h.const_mul 2).const_mul ((∫ x, |coordLaplacian K x|) * M)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => zero_le _) (fun m => hbound _ (by positivity))

/-- Large-time translation decay: translating the kernel changes the convolution of
`H_b f` by an `L¹`-small amount, along `b = n + 1`. -/
theorem tendsto_eLpNorm_horizontalMollify_heatSmoothed_translate_sub {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {ψ : Vec d → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    {f : FieldPair d → ℝ} (hf : Measurable f) (hfi : Integrable f Q) (z : Vec d) :
    Tendsto (fun n : ℕ => eLpNorm (fun ω =>
      horizontalMollify (fun x => ψ (x - z)) (heatSmoothed ((n + 1 : ℕ) : ℝ) f) ω -
        horizontalMollify ψ (heatSmoothed ((n + 1 : ℕ) : ℝ) f) ω) 1 Q) atTop (𝓝 0) := by
  have hψi : Integrable ψ volume := hψ.integrable_of_hasCompactSupport hψc
  set A : ℝ := (eLpNorm f 1 Q).toReal with hAdef
  have hA : 0 ≤ A := ENNReal.toReal_nonneg
  have hfA : eLpNorm f (ENNReal.ofReal 1) Q ≤ ENNReal.ofReal A := by
    rw [ENNReal.ofReal_one, hAdef, ENNReal.ofReal_toReal
      (memLp_one_iff_integrable.mpr hfi).eLpNorm_ne_top]
  set D : ℕ → ℝ := fun n => ∫ y, |euclideanHeatKernel ((n + 1 : ℕ) : ℝ) (y + -z) -
    euclideanHeatKernel ((n + 1 : ℕ) : ℝ) y| with hDdef
  have hbound (n : ℕ) : eLpNorm (fun ω =>
      horizontalMollify (fun x => ψ (x - z)) (heatSmoothed ((n + 1 : ℕ) : ℝ) f) ω -
        horizontalMollify ψ (heatSmoothed ((n + 1 : ℕ) : ℝ) f) ω) 1 Q ≤
      ENNReal.ofReal ((∫ x, |ψ x|) * (D n * A)) := by
    set b : ℝ := ((n + 1 : ℕ) : ℝ) with hbdef
    have hb : 0 < b := by positivity
    let k : Vec d → ℝ := fun y => euclideanHeatKernel b (y + -z) - euclideanHeatKernel b y
    have hΦ : Continuous (euclideanHeatKernel (d := d) b) := continuous_euclideanHeatKernel b
    have hkm : Measurable k :=
      ((hΦ.comp (continuous_id.add continuous_const)).sub hΦ).measurable
    have hΦi : Integrable (euclideanHeatKernel (d := d) b) volume :=
      integrable_euclideanHeatKernel hb
    have hΦzi : Integrable (fun y => euclideanHeatKernel (d := d) b (y + -z)) volume :=
      hΦi.comp_add_right (-z)
    have hki : Integrable k volume := hΦzi.sub hΦi
    have hHm : Measurable (heatSmoothed b f) :=
      (measurable_heatSmoothed_joint hf).comp (measurable_const.prodMk measurable_id)
    have hHi : Integrable (heatSmoothed b f) Q := by
      have h1 := eLpNorm_heatSmoothed_le Q hQ le_rfl hf hb.le
      rw [ENNReal.ofReal_one] at h1
      exact memLp_one_iff_integrable.mp ⟨hHm.aestronglyMeasurable,
        h1.trans_lt (memLp_one_iff_integrable.mpr hfi).eLpNorm_lt_top⟩
    have hHzm : Measurable (fun ρ => heatSmoothed b f (translate z ρ)) :=
      hHm.comp (Probability.measurable_translate z)
    have hHzi : Integrable (fun ρ => heatSmoothed b f (translate z ρ)) Q :=
      (measurePreserving_translate Q hQ z).integrable_comp_of_integrable hHi
    have hkfm : Measurable (horizontalMollify k f) := measurable_horizontalMollify k hkm hf
    -- the translated heat average differs by the convolution with `k`
    have hdiff : (fun ρ => heatSmoothed b f (translate z ρ) - heatSmoothed b f ρ) =ᵐ[Q]
        horizontalMollify k f := by
      have hΦzm : Measurable (fun y => euclideanHeatKernel (d := d) b (y + -z)) :=
        (hΦ.comp (continuous_id.add continuous_const)).measurable
      filter_upwards [ae_integrable_kernel_translate hQ hΦ.measurable hΦi hf hfi,
        ae_integrable_kernel_translate hQ hΦzm hΦzi hf hfi] with ρ h1 h2
      have hshift : heatSmoothed b f (translate z ρ) =
          ∫ y, euclideanHeatKernel b (y + -z) * f (translate y ρ) := by
        simp only [heatSmoothed, if_neg hb.ne', translate_add]
        have h := integral_add_right_eq_self (μ := (volume : Measure (Vec d)))
          (fun y => euclideanHeatKernel b (y + -z) * f (translate y ρ)) z
        simp only [add_neg_cancel_right] at h
        rw [← h]
      rw [hshift]
      simp only [heatSmoothed, if_neg hb.ne', horizontalMollify, k, sub_mul]
      exact (integral_sub h2 h1).symm
    -- bound the tested difference
    have hk1 : eLpNorm (horizontalMollify k f) (ENNReal.ofReal 1) Q ≤
        ENNReal.ofReal ((∫ x, |k x|) * A) :=
      (horizontalMollify_moment_le Q hQ le_rfl hA hkm hki hf hfA).2.2
    have hψk := (horizontalMollify_moment_le Q hQ le_rfl
      (mul_nonneg (integral_nonneg fun _ => abs_nonneg _) hA) hψ.measurable hψi hkfm hk1).2.2
    have heq : (fun ω =>
        horizontalMollify (fun x => ψ (x - z)) (heatSmoothed b f) ω -
          horizontalMollify ψ (heatSmoothed b f) ω) =ᵐ[Q]
        horizontalMollify ψ (horizontalMollify k f) := by
      filter_upwards [horizontalMollify_sub_ae hQ hψ.measurable hψi hHzm hHzi hHm hHi,
        horizontalMollify_congr_ae (K := ψ) hQ (hHzm.sub hHm) hkfm hdiff] with ω h1 h2
      rw [← horizontalMollify_comp_translate, ← h1]
      exact h2
    rw [eLpNorm_congr_ae heq]
    rw [ENNReal.ofReal_one] at hψk
    exact hψk
  have hlim : Tendsto (fun n => ENNReal.ofReal ((∫ x, |ψ x|) * (D n * A))) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.tendsto_ofReal ?_
    have h := ((tendsto_integral_abs_heatKernel_translate_sub (d := d) (-z)).mul_const A).const_mul
      (∫ x, |ψ x|)
    rw [zero_mul, mul_zero] at h
    exact h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => zero_le _) hbound

end EinsteinRelation.Correctors
