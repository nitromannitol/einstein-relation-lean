import EinsteinFull.Calculus.C20TubeWeightedGradientEnergyLimit
import EinsteinFull.Calculus.C18TubeNonlinearCompactTimeLimits

open EinsteinRelation MeasureTheory Filter EinsteinFull.External.Source.GMP
open scoped Topology

namespace EinsteinFull.Calculus

/-- Lᵖ membership is invariant under a nondegenerate affine change of time. -/
theorem c20_memLp_affine_time_pullback_iff {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] (t k : ℝ) (hk : 0 < k)
    (S : Set (ℝ × Vec d)) (hS : MeasurableSet S) (p : ENNReal)
    (f : ℝ × Vec d → E) :
    MemLp (fun z => f (t + k * z.1, z.2)) p
      (volume.restrict ((fun z : ℝ × Vec d => (t + k * z.1, z.2)) ⁻¹' S)) ↔
    MemLp f p (volume.restrict S) := by
  let e : (ℝ × Vec d) ≃ᵐ (ℝ × Vec d) :=
    { toFun := fun z => (t + k * z.1, z.2)
      invFun := fun z => ((z.1 - t) / k, z.2)
      left_inv := by
        intro z
        simp [add_sub_cancel_left, mul_div_cancel_left₀ _ (ne_of_gt hk)]
      right_inv := by
        intro z
        simp [mul_div_cancel₀ _ (ne_of_gt hk)]
      measurable_toFun :=
        ((measurable_const_mul k).comp measurable_fst |>.const_add t).prodMk measurable_snd
      measurable_invFun :=
        ((measurable_fst.sub measurable_const).div_const k).prodMk measurable_snd }
  constructor
  · intro hf
    have hm : MemLp f p (ENNReal.ofReal |k⁻¹| • volume.restrict S) := by
      rw [← c20_map_restrict_volume_affine_time_prod t k (ne_of_gt hk) S hS]
      exact (e.memLp_map_measure_iff).2 hf
    have hn : ENNReal.ofReal |k⁻¹| ≠ 0 := by simp [ne_of_gt hk]
    have ht := hm.smul_measure (c := (ENNReal.ofReal |k⁻¹|)⁻¹)
      (ENNReal.inv_ne_top.mpr hn)
    rw [smul_smul, ENNReal.inv_mul_cancel hn ENNReal.ofReal_ne_top, one_smul] at ht
    exact ht
  · exact c20_memLp_affine_time_pullback t k (ne_of_gt hk) S hS p f

/-- A global L² field has L² forward averages on a bounded time cylinder. -/
theorem c20_forward_average_eventually_memLp_global
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {r a b : ℝ} (hab : a < b) (y : Vec d)
    (u : ℝ × Vec d → E) (hu : MemLp u 2 volume) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, MemLp
      (fun z => h⁻¹ • ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)) 2
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall y r)) := by
  let t : ℝ := (a + b) / 2
  let k : ℝ := b - a
  have hk : 0 < k := by dsimp [k]; linarith
  let A : ℝ × Vec d → ℝ × Vec d := fun z => (t + k * z.1, z.2)
  let S : Set (ℝ × Vec d) := Set.Ioo a b ×ˢ sourceBall y r
  let I : Set (ℝ × Vec d) := Set.Ioo (-1/2 : ℝ) (1/2) ×ˢ sourceBall y r
  let J : Set (ℝ × Vec d) := Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall y r
  have ha : t + k * (-1/2) = a := by dsimp [t, k]; ring
  have hb : t + k * (1/2) = b := by dsimp [t, k]; ring
  have hpre : A ⁻¹' S = I := by
    simpa only [A, S, I, ha, hb] using
      c20_affine_time_preimage_slab t k (-1/2) (1/2) hk (sourceBall y r)
  have hS : MeasurableSet S := measurableSet_Ioo.prod (c20_sourceBall_measurable y r)
  have huA : MemLp (fun z => u (A z)) 2 (volume.restrict J) := by
    have h := c20_memLp_affine_time_pullback t k (ne_of_gt hk) Set.univ
      MeasurableSet.univ 2 u (by simpa using hu)
    have h' : MemLp (fun z => u (A z)) 2 volume := by simpa [A] using h
    exact h'.mono_measure Measure.restrict_le_self
  letI := c18_smallSourceCylinder_isFiniteMeasure y r
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0, h / k < 1 / 4 :=
    (c20_tendsto_positive_time_div k hk).eventually
      ((eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4)).filter_mono nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin, hsmall] with h hh hs
  have havg := c18_memLp_forward_average (c20_sourceBall_measurable y r)
    (div_pos hh hk) (le_of_lt hs) huA
  apply (c20_memLp_affine_time_pullback_iff t k hk S hS 2 _).mp
  rw [show (fun z : ℝ × Vec d => (t + k * z.1, z.2)) ⁻¹' S = I from hpre]
  convert havg using 1
  funext z
  have hav := c20_forward_average_affine_spacetime u t k (h/k) (ne_of_gt hk) z
  simp only [mul_div_cancel₀ h (ne_of_gt hk)] at hav
  simpa only [A, hav]
  dsimp [I]
  congr 2 <;> norm_num

/-- A bounded vector test turns an elliptic flux of an L² vector field into an L² scalar. -/
theorem c20_elliptic_flux_test_memLp
    {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : IsUniformlyElliptic κ ρ α) (μ : Measure (ℝ × Vec d))
    (G V : ℝ × Vec d → Vec d) (hGm : AEStronglyMeasurable G μ)
    (hG : MemLp (fun z => euclideanNorm (G z)) 2 μ)
    (hVm : AEStronglyMeasurable V μ) (C : ℝ)
    (hVb : ∀ᵐ z ∂μ, euclideanNorm (V z) ≤ C) :
    MemLp (fun z => dot ((α z.2).mulVec (G z)) (V z)) 2 μ := by
  have hm : AEStronglyMeasurable (fun z => dot ((α z.2).mulVec (G z)) (V z)) μ := by
    change AEStronglyMeasurable (fun z => ∑ i : Fin d, (∑ j : Fin d,
      α z.2 i j * G z j) * V z i) μ
    have hm' : AEStronglyMeasurable (∑ i : Fin d, fun z => (∑ j : Fin d,
        α z.2 i j * G z j) * V z i) μ := by
      apply Finset.aestronglyMeasurable_sum
      intro i hi
      apply AEStronglyMeasurable.mul _ ((continuous_apply i).comp_aestronglyMeasurable hVm)
      have hjm : AEStronglyMeasurable (∑ j : Fin d, fun z => α z.2 i j * G z j) μ := by
        apply Finset.aestronglyMeasurable_sum
        intro j hj
        apply AEStronglyMeasurable.mul _ ((continuous_apply j).comp_aestronglyMeasurable hGm)
        let : MeasurableSpace (Mat d) := EinsteinRelation.instMeasurableSpaceMat d
        let : BorelSpace (Mat d) := EinsteinRelation.instBorelSpaceMat d
        exact ((((continuous_id : Continuous (id : Mat d → Mat d)).matrix_elem i j).measurable.comp
          hell.2.1).comp measurable_snd).aestronglyMeasurable
      convert hjm using 1
      ext z
      simp only [Finset.sum_apply]
    convert hm' using 1
    ext z
    simp only [Finset.sum_apply]
  apply (hG.const_mul (κ⁻¹ * C)).mono' hm
  filter_upwards [hVb] with z hz
  rw [Real.norm_eq_abs]
  have hcomm : dot ((α z.2).mulVec (G z)) (V z) =
      dot (V z) ((α z.2).mulVec (G z)) := by simp only [dot, mul_comm]
  rw [hcomm]
  have hb := c20_elliptic_bilinear_bound hκ ρ α hell z.2 (V z) (G z)
  have hv : 0 ≤ euclideanNorm (V z) := Real.sqrt_nonneg _
  have hg : 0 ≤ euclideanNorm (G z) := Real.sqrt_nonneg _
  have hC : 0 ≤ C := hv.trans hz
  have hk : 0 ≤ κ⁻¹ := le_of_lt (inv_pos.mpr hκ)
  exact hb.trans (by gcongr)

/-- A nonlinear derivative and an elliptic L² flux have an integrable pairing. -/
theorem c20_nonlinear_flux_test_integrable
    {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : IsUniformlyElliptic κ ρ α) (μ : Measure (ℝ × Vec d)) [IsFiniteMeasure μ]
    (u : ℝ × Vec d → ℝ) (hu : MemLp u 2 μ)
    (G V : ℝ × Vec d → Vec d) (hGm : AEStronglyMeasurable G μ)
    (hG : MemLp (fun z => euclideanNorm (G z)) 2 μ)
    (hVm : AEStronglyMeasurable V μ) (C : ℝ)
    (hVb : ∀ᵐ z ∂μ, euclideanNorm (V z) ≤ C)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (M : ℝ)
    (hF2 : ∀ s, |deriv (deriv F) s| ≤ M) :
    Integrable (fun z => deriv F (u z) * dot ((α z.2).mulVec (G z)) (V z)) μ := by
  exact (c20_deriv_comp_memLp u hu F hF M hF2).integrable_mul
    (c20_elliptic_flux_test_memLp hκ ρ α hell μ G V hGm hG hVm C hVb)

/-- Any bounded source cylinder has finite Lebesgue measure. -/
theorem c20_sourceCylinder_isFiniteMeasure {d : ℕ} (a b r : ℝ) (y : Vec d) :
    IsFiniteMeasure (volume.restrict (Set.Ioo a b ×ˢ sourceBall y r)) := by
  haveI : IsFiniteMeasure (volume.restrict (sourceBall y r)) :=
    isFiniteMeasure_restrict.mpr (c18_sourceBall_measure_ne_top y r)
  have hf : IsFiniteMeasure ((volume.restrict (Set.Ioo a b)).prod
      (volume.restrict (sourceBall y r))) := inferInstance
  rwa [Measure.prod_restrict] at hf

/-- Compactly supported bounded weights make the nonlinear forward scalar integrable. -/
theorem c20_nonlinear_scalar_eventually_integrable_compact
    {d : ℕ} {r a b : ℝ} (hab : a < b) (y : Vec d)
    (u : ℝ × Vec d → ℝ)
    (hu : MemLp u 2 (volume.restrict (Set.Ioo a b ×ˢ sourceBall y r)))
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (M : ℝ) (hM : 0 ≤ M)
    (hF2 : ∀ s, |deriv (deriv F) s| ≤ M)
    (w ψ : ℝ × Vec d → ℝ) (C : ℝ) (hw : Measurable w)
    (hwb : ∀ z, |w z| ≤ C) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ Set.Ioo a b ×ˢ sourceBall y r)
    (hwzero : ∀ z, z ∉ tsupport ψ → w z = 0) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, Integrable (fun z =>
      w z * F (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)))
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall y r)) := by
  let S : Set (ℝ × Vec d) := Set.Ioo a b ×ˢ sourceBall y r
  have hS : MeasurableSet S := measurableSet_Ioo.prod (c20_sourceBall_measurable y r)
  have hu0 : MemLp (S.indicator u) 2 volume := (memLp_indicator_iff_restrict hS).2 hu
  letI := c20_sourceCylinder_isFiniteMeasure a b r y
  have havg := c20_forward_average_eventually_memLp_global (r := r) hab y (S.indicator u) hu0
  obtain ⟨δ, hδ, heq⟩ := c20_compact_support_forward_indicator_integral ψ hψc hψs u
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0, h < δ :=
    (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds
  filter_upwards [havg, self_mem_nhdsWithin, hsmall] with h hav hp hd
  have hint := (c20_nonlinear_comp_integrable _ (by simpa only [smul_eq_mul] using hav)
    F hF M hM hF2).bdd_mul hw.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hwb z))
  apply hint.congr
  filter_upwards with z
  by_cases hz : z ∈ tsupport ψ
  · rw [heq z hz h ⟨le_of_lt hp, le_of_lt hd⟩]
  · simp [hwzero z hz]

/-- Compactly tested nonlinear fluxes of forward averages are integrable. -/
theorem c20_nonlinear_flux_eventually_integrable_compact
    {d : ℕ} {κ r a b : ℝ} (hκ : 0 < κ) (hab : a < b)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α) (y : Vec d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : MemLp u 2 (volume.restrict (Set.Ioo a b ×ˢ sourceBall y r)))
    (hGm : AEStronglyMeasurable G (volume.restrict (Set.Ioo a b ×ˢ sourceBall y r)))
    (hG : MemLp (fun z => euclideanNorm (G z)) 2
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall y r)))
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (M : ℝ)
    (hF2 : ∀ s, |deriv (deriv F) s| ≤ M)
    (V : ℝ × Vec d → Vec d) (C : ℝ) (hVm : Measurable V)
    (hVb : ∀ z, euclideanNorm (V z) ≤ C)
    (ψ : ℝ × Vec d → ℝ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ Set.Ioo a b ×ˢ sourceBall y r)
    (hVzero : ∀ z, z ∉ tsupport ψ → V z = 0) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, Integrable (fun z =>
      deriv F (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)) *
      dot ((α z.2).mulVec (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2))) (V z))
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall y r)) := by
  let S : Set (ℝ × Vec d) := Set.Ioo a b ×ˢ sourceBall y r
  have hS : MeasurableSet S := measurableSet_Ioo.prod (c20_sourceBall_measurable y r)
  obtain ⟨hu0, hGm0, hG0⟩ := c20_memLp_zero_extension S hS u G hu hGm hG
  have hvec := c20_vector_memLp_of_euclidean (S.indicator G) hGm0 hG0
  letI := c20_sourceCylinder_isFiniteMeasure a b r y
  have huavg := c20_forward_average_eventually_memLp_global (r := r) hab y (S.indicator u) hu0
  have hGavg := c20_forward_average_eventually_memLp_global (r := r) hab y (S.indicator G) hvec
  obtain ⟨δ, hδ, heq⟩ := c20_compact_support_zero_extension_fields ψ hψc hψs u G
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0, h < δ :=
    (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds
  have hc : Continuous (fun v : Vec d => euclideanNorm v) := by
    unfold euclideanNorm euclideanSq dot
    exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ =>
      (continuous_apply i).mul (continuous_apply i))
  filter_upwards [huavg, hGavg, self_mem_nhdsWithin, hsmall] with h hu' hG' hp hd
  have hGnorm : MemLp (fun z => euclideanNorm
      (h⁻¹ • ∫ s in (0 : ℝ)..h, S.indicator G (z.1+s,z.2))) 2 (volume.restrict S) := by
    apply (hG'.norm.const_mul ((d : ℝ) + 1)).mono'
      (hc.comp_aestronglyMeasurable hG'.aestronglyMeasurable)
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ euclideanNorm
      (h⁻¹ • ∫ s in (0 : ℝ)..h, S.indicator G (z.1+s,z.2)) from Real.sqrt_nonneg _)]
    exact euclideanNorm_le_dimension_mul_norm _
  have hint := c20_nonlinear_flux_test_integrable hκ ρ α hell (volume.restrict S)
    _ (by simpa only [smul_eq_mul] using hu') _ V hG'.aestronglyMeasurable hGnorm
    hVm.aestronglyMeasurable C (Filter.Eventually.of_forall hVb) F hF M hF2
  apply hint.congr
  filter_upwards with z
  by_cases hz : z ∈ tsupport ψ
  · obtain ⟨hu'', hG'', _, _⟩ := heq h ⟨le_of_lt hp, le_of_lt hd⟩ z hz
    rw [hu'', hG'']
  · rw [hVzero z hz]
    simp [dot]

/-- All three terms of the tested forward nonlinear pairing are integrable. -/
theorem c20_tested_forward_nonlinear_eventually_integrable
    {d : ℕ} {κ r a b : ℝ} (hκ : 0 < κ) (hab : a < b)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : IsUniformlyElliptic κ ρ α) (y : Vec d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : MemLp u 2 (volume.restrict (Set.Ioo a b ×ˢ sourceBall y r)))
    (hGm : AEStronglyMeasurable G (volume.restrict (Set.Ioo a b ×ˢ sourceBall y r)))
    (hG : MemLp (fun z => euclideanNorm (G z)) 2
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall y r)))
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (M : ℝ) (hM : 0 ≤ M)
    (hder : ∀ s, |deriv (deriv F) s| ≤ M)
    (ψ : ℝ × Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ Set.Ioo a b ×ˢ sourceBall y r) :
    let uh := fun h : ℝ => fun z : ℝ × Vec d => h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)
    let Gh := fun h : ℝ => fun z : ℝ × Vec d => h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)
    ∀ᶠ h : ℝ in nhdsWithin 0 (Set.Ioi 0),
      Integrable (fun z : ℝ × Vec d => -(ρ z.2 * F (uh h z)) * fderiv ℝ ψ z (1,0) +
        deriv F (uh h z) * dot ((α z.2).mulVec (Gh h z))
          (fun j => fderiv ℝ ψ z (0,unitVector j)) +
        deriv (deriv F) (uh h z) * dot ((α z.2).mulVec (Gh h z)) (Gh h z) * ψ z)
        (volume.restrict (Set.Ioo a b ×ˢ sourceBall y r)) := by
  dsimp only
  let χ : ℝ × Vec d → ℝ := fun z => fderiv ℝ ψ z (1,0)
  let w : ℝ × Vec d → ℝ := fun z => -ρ z.2 * χ z
  let V : ℝ × Vec d → Vec d := fun z j => fderiv ℝ ψ z (0,unitVector j)
  have hχ : Continuous χ := (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hχc : HasCompactSupport χ := hψc.fderiv_apply ℝ (1,0)
  obtain ⟨C, hC⟩ := hχ.bounded_above_of_compact_support hχc
  have hρ : ∀ x, |ρ x| ≤ κ⁻¹ := by
    intro x
    rw [abs_of_nonneg (le_trans (le_of_lt hκ) (hell.2.2 x).1)]
    exact (hell.2.2 x).2.1
  have hw : Measurable w := ((hell.1.comp measurable_snd).neg).mul hχ.measurable
  have hwb : ∀ z, |w z| ≤ κ⁻¹ * max C 0 := by
    intro z
    dsimp only [w]
    rw [abs_mul, abs_neg]
    have hc : |χ z| ≤ max C 0 := by
      simpa only [Real.norm_eq_abs] using (hC z).trans (le_max_left C 0)
    exact mul_le_mul (hρ z.2) hc (abs_nonneg _) (le_of_lt (inv_pos.mpr hκ))
  have hwzero : ∀ z, z ∉ tsupport ψ → w z = 0 := by
    intro z hz
    simp [w, χ, fderiv_of_notMem_tsupport ℝ hz]
  obtain ⟨hVm, ⟨D, hD, hVb⟩, hVz⟩ := c18_compact_test_spatial_derivative_bounded ψ hψ hψc
  have hs := c20_nonlinear_scalar_eventually_integrable_compact hab y u hu F hF M hM hder
    w ψ (κ⁻¹ * max C 0) hw hwb hψc hψs hwzero
  have hf := c20_nonlinear_flux_eventually_integrable_compact hκ hab ρ α hell y u G hu hGm hG
    F hF M hder V D hVm hVb ψ hψc hψs hVz
  have hg := c20_nonlinear_forward_gradient_energy_eventually_integrable_compact
    hκ hab ρ α hell y u G hu hGm hG F hF M hder ψ hψ hψc hψs
  filter_upwards [hs, hf, hg] with h hsi hfi hgi
  convert (hsi.add hfi).add hgi using 1 <;> funext z <;> dsimp [w, χ, V] <;> ring

/-- The three nonlinear weak-pairing terms converge on compactly tested cylinders. -/
theorem c20_weighted_forward_nonlinear_weak_pairing_limit_compact
    {d : ℕ} {κ r a b : ℝ} (hκ : 0 < κ) (hr : 0 < r) (hab : a < b)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : IsUniformlyElliptic κ ρ α) (y : Vec d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : MemLp u 2 (volume.restrict (Set.Ioo a b ×ˢ sourceBall y r)))
    (hGm : AEStronglyMeasurable G (volume.restrict (Set.Ioo a b ×ˢ sourceBall y r)))
    (hG : MemLp (fun z => euclideanNorm (G z)) 2
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall y r)))
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (M : ℝ) (hM : 0 ≤ M)
    (hder : ∀ s, |deriv (deriv F) s| ≤ M)
    (ψ : ℝ × Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ Set.Ioo a b ×ˢ sourceBall y r) :
    let uh := fun h : ℝ => fun z : ℝ × Vec d => h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)
    let Gh := fun h : ℝ => fun z : ℝ × Vec d => h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)
    Tendsto (fun h : ℝ => ∫ z in Set.Ioo a b ×ˢ sourceBall y r,
      -(ρ z.2 * F (uh h z)) * fderiv ℝ ψ z (1,0) +
        deriv F (uh h z) * dot ((α z.2).mulVec (Gh h z))
          (fun j => fderiv ℝ ψ z (0,unitVector j)) +
        deriv (deriv F) (uh h z) * dot ((α z.2).mulVec (Gh h z)) (Gh h z) * ψ z)
      (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 (∫ z in Set.Ioo a b ×ˢ sourceBall y r,
        -(ρ z.2 * F (u z)) * fderiv ℝ ψ z (1,0) +
        deriv F (u z) * dot ((α z.2).mulVec (G z))
          (fun j => fderiv ℝ ψ z (0,unitVector j)) +
        deriv (deriv F) (u z) * dot ((α z.2).mulVec (G z)) (G z) * ψ z)) := by
  dsimp only
  let S : Set (ℝ × Vec d) := Set.Ioo a b ×ˢ sourceBall y r
  let μ := volume.restrict S
  let χ : ℝ × Vec d → ℝ := fun z => fderiv ℝ ψ z (1,0)
  let w : ℝ × Vec d → ℝ := fun z => -ρ z.2 * χ z
  let V : ℝ × Vec d → Vec d := fun z j => fderiv ℝ ψ z (0,unitVector j)
  letI : IsFiniteMeasure μ := c20_sourceCylinder_isFiniteMeasure a b r y
  have hχ : Continuous χ := (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hχc : HasCompactSupport χ := hψc.fderiv_apply ℝ (1,0)
  obtain ⟨C, hC⟩ := hχ.bounded_above_of_compact_support hχc
  have hρ : ∀ x, |ρ x| ≤ κ⁻¹ := by
    intro x
    rw [abs_of_nonneg (le_trans (le_of_lt hκ) (hell.2.2 x).1)]
    exact (hell.2.2 x).2.1
  have hw : Measurable w := ((hell.1.comp measurable_snd).neg).mul hχ.measurable
  have hwb : ∀ z, |w z| ≤ κ⁻¹ * max C 0 := by
    intro z
    dsimp only [w]
    rw [abs_mul, abs_neg]
    have hc : |χ z| ≤ max C 0 := by
      simpa only [Real.norm_eq_abs] using (hC z).trans (le_max_left C 0)
    exact mul_le_mul (hρ z.2) hc (abs_nonneg _) (le_of_lt (inv_pos.mpr hκ))
  have hwzero : ∀ z, z ∉ tsupport ψ → w z = 0 := by
    intro z hz
    simp [w, χ, fderiv_of_notMem_tsupport ℝ hz]
  obtain ⟨hVm, ⟨D, hD, hVb⟩, hVz⟩ := c18_compact_test_spatial_derivative_bounded ψ hψ hψc
  have hs0 : Integrable (fun z => -(ρ z.2 * F (u z)) * χ z) μ := by
    have hi := (c20_nonlinear_comp_integrable u hu F hF M hM hder).bdd_mul
      hw.aestronglyMeasurable (Filter.Eventually.of_forall fun z => by
        simpa only [Real.norm_eq_abs] using hwb z)
    convert hi using 1 <;> funext z <;> dsimp [w, χ] <;> ring
  have hse : ∀ᶠ h : ℝ in 𝓝[>] 0, Integrable (fun z =>
      -(ρ z.2 * F (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2))) * χ z) μ := by
    have hi := c20_nonlinear_scalar_eventually_integrable_compact hab y u hu F hF M hM hder
      w ψ (κ⁻¹ * max C 0) hw hwb hψc hψs hwzero
    filter_upwards [hi] with h hh
    convert hh using 1 <;> funext z <;> dsimp [w, χ] <;> ring
  have hf0 := c20_nonlinear_flux_test_integrable hκ ρ α hell μ u hu G V hGm hG
    hVm.aestronglyMeasurable D (Filter.Eventually.of_forall hVb) F hF M hder
  have hfe := c20_nonlinear_flux_eventually_integrable_compact hκ hab ρ α hell y u G hu hGm hG
    F hF M hder V D hVm hVb ψ hψc hψs hVz
  obtain ⟨E, hE⟩ := hψ.continuous.bounded_above_of_compact_support hψc
  have hg0 := c20_nonlinear_gradient_energy_integrable hκ ρ α hell μ u hu.aestronglyMeasurable
    G hGm hG F hF M hder ψ hψ.continuous.aestronglyMeasurable E
    (Filter.Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hE z))
  have hge := c20_nonlinear_forward_gradient_energy_eventually_integrable_compact
    hκ hab ρ α hell y u G hu hGm hG F hF M hder ψ hψ hψc hψs
  have hs := c18_weighted_forward_nonlinear_scalar_limit_compact hκ hab ρ α hell y u hu
    F hF M hM hder ψ hψ hψc hψs
  have hfl := c18_weighted_forward_nonlinear_flux_derivative_limit_compact
    hκ hr hab ρ α hell y u G hu hGm hG F hF M hM hder ψ hψ hψc hψs
  have hf := c20_weighted_integral_of_L1_limit
    (fun h z => deriv F (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)) *
      dot ((α z.2).mulVec (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2))) (V z))
    (fun z => deriv F (u z) * dot ((α z.2).mulVec (G z)) (V z))
    (fun _ => 1) 1 (by fun_prop) (by simp) hfe hf0 hfl
  have hg := c20_weighted_forward_nonlinear_gradient_energy_integral_limit_compact
    hκ hr hab ρ α hell y u G hu hGm hG F hF M hM hder ψ hψ hψc hψs
  have ht := (hs.add (by simpa only [one_mul] using hf)).add hg
  have hi0 := integral_add hs0 hf0
  have hi1 := integral_add (hs0.add hf0) hg0
  simp only [Pi.add_apply] at hi0 hi1
  rw [← hi0, ← hi1] at ht
  have htotal := c20_tested_forward_nonlinear_eventually_integrable
    hκ hab ρ α hell y u G hu hGm hG F hF M hM hder ψ hψ hψc hψs
  apply ht.congr'
  filter_upwards [hse, hfe, hge, htotal] with h hsi hfi hgi hti
  have hsum := hti.sub hgi
  have hsum' : Integrable (fun z =>
      -(ρ z.2 * F (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2))) * χ z +
      deriv F (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)) *
        dot ((α z.2).mulVec (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2))) (V z)) μ := by
    convert hsum using 1 <;> funext z <;> dsimp [χ, V] <;> ring
  have hi2 := integral_add hsi hfi
  have hi3 := integral_add hsum' hgi
  rw [hi3, hi2]

end EinsteinFull.Calculus
