import EinsteinFull.Calculus.C9GMPStrongCompactGenerator
open MeasureTheory Filter Set ProbabilityTheory
open scoped NNReal ENNReal Topology BigOperators BoundedContinuousFunction
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.External.GantertSection7Support EinsteinFull.Work.W5
open EinsteinFull.C8GMP
open scoped InnerProductSpace

private def dynkinActionCLM {d : ℕ} (hd : 2 ≤ d)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) {ω : FieldPair d} {hω : IsRegular Λ ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (R : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
    (t : ℝ≥0) :
    Lp ℝ 2 (physicalReversibleMeasure ω hd lam) →L[ℝ]
      Lp ℝ 2 (physicalReversibleMeasure ω hd lam) :=
  LinearMap.mkContinuous
    { toFun := R.kernelL2Action hd hΛ t
      map_add' := fun f g => by
        apply ext_inner_right ℝ
        intro u
        rw [← kernelL2Action_symmetric hd hΛ R, inner_add_left,
          inner_add_left, ← kernelL2Action_symmetric hd hΛ R,
          ← kernelL2Action_symmetric hd hΛ R]
      map_smul' := fun c f => by
        apply ext_inner_right ℝ
        intro u
        rw [← kernelL2Action_symmetric hd hΛ R, inner_smul_left,
          inner_smul_left, ← kernelL2Action_symmetric hd hΛ R]
        simp }
    1 (fun f => by
      change ‖R.kernelL2Action hd hΛ t f‖ ≤ 1 * ‖f‖
      rw [one_mul]
      exact R.kernelL2Action_norm_le hd hΛ t f)

private theorem dynkinAction_zero {d : ℕ} (hd : 2 ≤ d)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) {ω : FieldPair d} {hω : IsRegular Λ ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (R : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1) :
    dynkinActionCLM hd hΛ R 0 = ContinuousLinearMap.id ℝ _ := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  letI : SigmaFinite (physicalReversibleMeasure ω hd lam) :=
    EinsteinRelation.Diffusion.physicalReversibleMeasure_sigmaFinite hd ω lam
  letI : IsMarkovKernel (R.transitionKernel 0) := R.transitionKernel_isMarkovKernel 0
  have hk := WeightedKernelL2.kernelIntegralL2_coe
    (R.transitionKernel_invariant hd hΛ 0) f
  change R.kernelL2Action hd hΛ 0 f =ᵐ[_] _ at hk
  filter_upwards [hk] with x hx
  change R.kernelL2Action hd hΛ 0 f x = f x
  rw [hx]
  simp only [WeightedKernelL2.kernelIntegral, R.transitionKernel_zero,
    Kernel.id_apply, integral_dirac]

private theorem dynkinOrbit_continuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : ℝ≥0 → E →L[ℝ] E}
    (hP0 : P 0 = ContinuousLinearMap.id ℝ E)
    (hPm : ∀ s t, P (s + t) = (P s).comp (P t))
    (hPn : ∀ t f, ‖P t f‖ ≤ ‖f‖)
    (f : E) (hPc : Tendsto (fun t => P t f) (𝓝[>] (0 : ℝ≥0)) (𝓝 f)) : Continuous (fun t => P t f) := by
  have hc0 : Tendsto (fun t => P t f) (𝓝 (0 : ℝ≥0)) (𝓝 f) := by
    have hs : Tendsto (fun t => P t f) (𝓝[{0}] (0 : ℝ≥0)) (𝓝 f) := by
      simpa only [hP0, ContinuousLinearMap.id_apply] using
        (continuousWithinAt_singleton (f := fun t => P t f) (x := 0)).tendsto
    have h := hPc.sup hs
    have he : Ici (0 : ℝ≥0) = univ := Set.eq_univ_of_forall (fun t => t.property)
    simpa only [nhdsGT_sup_nhdsWithin_singleton, he, nhdsWithin_univ] using h
  apply continuous_iff_continuousAt.mpr
  intro t
  have hleft : Tendsto (fun s : ℝ≥0 => ‖P (s - t) f - f‖) (𝓝 t) (𝓝 0) := by
    have hz : Tendsto (fun s : ℝ≥0 => s - t) (𝓝 t) (𝓝 0) := by
      have h : Tendsto (fun s : ℝ≥0 => s - t) (𝓝 t) (𝓝 (t - t)) :=
        (show Continuous (fun s : ℝ≥0 => s - t) from
          continuous_id.sub continuous_const).continuousAt
      rwa [tsub_self] at h
    simpa using ((hc0.comp hz).sub (tendsto_const_nhds (x := f))).norm
  have hright : Tendsto (fun s : ℝ≥0 => ‖P (t - s) f - f‖) (𝓝 t) (𝓝 0) := by
    have hz : Tendsto (fun s : ℝ≥0 => t - s) (𝓝 t) (𝓝 0) := by
      have h : Tendsto (fun s : ℝ≥0 => t - s) (𝓝 t) (𝓝 (t - t)) :=
        (show Continuous (fun s : ℝ≥0 => t - s) from
          continuous_const.sub continuous_id).continuousAt
      rwa [tsub_self] at h
    simpa using ((hc0.comp hz).sub (tendsto_const_nhds (x := f))).norm
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun s => dist_nonneg) _ (by simpa using hleft.add hright)
  intro s
  rcases le_total t s with h | h
  · have he : P s f - P t f = P t (P (s - t) f - f) := by
      rw [map_sub, ← ContinuousLinearMap.comp_apply, ← hPm, add_tsub_cancel_of_le h]
    rw [dist_eq_norm, he]
    exact (hPn t _).trans (le_add_of_nonneg_right (norm_nonneg _))
  · have he : P t f - P s f = P s (P (t - s) f - f) := by
      rw [map_sub, ← ContinuousLinearMap.comp_apply, ← hPm, add_tsub_cancel_of_le h]
    rw [dist_comm, dist_eq_norm, he]
    exact (hPn s _).trans (le_add_of_nonneg_left (norm_nonneg _))

private theorem dynkinOrbit_tendsto_of_generator
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : ℝ≥0 → E →L[ℝ] E} {f g : E}
    (hg : Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (P t f - f))
      (𝓝[>] (0 : ℝ≥0)) (𝓝 g)) :
    Tendsto (fun t => P t f) (𝓝[>] (0 : ℝ≥0)) (𝓝 f) := by
  have ht : Tendsto (fun t : ℝ≥0 => (t : ℝ)) (𝓝[>] (0 : ℝ≥0)) (𝓝 (0 : ℝ)) :=
    continuous_subtype_val.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h := (ht.smul hg).add_const f
  simp only [zero_smul, zero_add] at h
  apply h.congr'
  filter_upwards [eventually_mem_nhdsWithin] with t ht
  rw [smul_inv_smul₀ (NNReal.coe_ne_zero.mpr (ne_of_gt ht)), sub_add_cancel]

private theorem dynkinOrbit_hasDeriv_right
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : ℝ≥0 → E →L[ℝ] E}
    (hPm : ∀ s t, P (s + t) = (P s).comp (P t))
    {f g : E}
    (hg : Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (P t f - f))
      (𝓝[>] (0 : ℝ≥0)) (𝓝 g)) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s : ℝ => P s.toNNReal f)
      (P t.toNNReal g) (Ioi t) t := by
  apply (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl t)).mpr
  have hsub : Tendsto (fun s : ℝ => (s - t).toNNReal)
      (𝓝[>] t) (𝓝[>] (0 : ℝ≥0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [Function.comp_apply, sub_self, Real.toNNReal_zero] using
        (show Continuous (fun s : ℝ => (s - t).toNNReal) from
          continuous_real_toNNReal.comp (continuous_id.sub continuous_const)).continuousAt.tendsto.mono_left
          (show 𝓝[>] t ≤ 𝓝 t from nhdsWithin_le_nhds)
    · filter_upwards [eventually_mem_nhdsWithin] with s hs
      exact Real.toNNReal_pos.mpr (sub_pos.mpr hs)
  have h := ((P t.toNNReal).continuous.tendsto g).comp (hg.comp hsub)
  apply h.congr'
  filter_upwards [eventually_mem_nhdsWithin] with s hs
  change t < s at hs
  have hs0 : 0 ≤ s := ht.trans hs.le
  have he : t.toNNReal + (s - t).toNNReal = s.toNNReal := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_add, Real.coe_toNNReal', max_eq_left ht,
      max_eq_left (sub_nonneg.mpr hs.le), max_eq_left hs0]
    exact add_sub_cancel _ _
  simp only [Function.comp_apply, map_smul, map_sub,
    slope_def_module, Real.coe_toNNReal', max_eq_left (sub_nonneg.mpr hs.le)]
  rw [← ContinuousLinearMap.comp_apply, ← hPm, he]

private theorem dynkinOrbit_integral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : ℝ≥0 → E →L[ℝ] E}
    (hP0 : P 0 = ContinuousLinearMap.id ℝ E)
    (hPm : ∀ s t, P (s + t) = (P s).comp (P t))
    (hPn : ∀ t f, ‖P t f‖ ≤ ‖f‖)
    {f g : E}
    (hg : Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (P t f - f))
      (𝓝[>] (0 : ℝ≥0)) (𝓝 g))
    (hc : Tendsto (fun t => P t g) (𝓝[>] (0 : ℝ≥0)) (𝓝 g)) (T : ℝ≥0) :
    P T f - f = ∫ s in (0 : ℝ)..(T : ℝ), P s.toNNReal g := by
  have hf := dynkinOrbit_continuous hP0 hPm hPn f (dynkinOrbit_tendsto_of_generator hg)
  have hgc := dynkinOrbit_continuous hP0 hPm hPn g hc
  have he := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
    (f := fun s : ℝ => P s.toNNReal f) (a := (0 : ℝ)) (b := (T : ℝ)) T.property (hf.comp continuous_real_toNNReal).continuousOn
    (fun t ht => dynkinOrbit_hasDeriv_right hPm hg t ht.1.le)
    ((hgc.comp continuous_real_toNNReal).intervalIntegrable (0 : ℝ) (T : ℝ))
  simpa only [Function.comp_apply, Real.toNNReal_coe, Real.toNNReal_zero, hP0,
    ContinuousLinearMap.id_apply] using he.symm

/-- Integrated evolution for the actual L² action and a literal compact smooth test. -/
theorem gmp_compact_test_integrated_evolution
    {d : ℕ} (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    {ω : FieldPair d} {hω : IsRegular Λ ω} {lam : ℝ}
    {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (R : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
    (hSmooth : IsSmoothFieldPair ω)
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (f0 : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hrep : (f0 : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] f)
    (T : ℝ≥0) :
    R.kernelL2Action hd hΛ T f0 - f0 =
      ∫ s in (0 : ℝ)..(T : ℝ), R.kernelL2Action hd hΛ s.toNNReal
        (compactTestGeneratorL2 hd ω hSmooth lam f hf hc) := by
  let P := dynkinActionCLM hd hΛ R
  let g := physicalGenerator (firstCoordinateIndex hd) ω lam f
  have hgf : ContDiff ℝ (⊤ : ℕ∞) g :=
    gantert_contDiff_physicalGenerator _ ω hSmooth lam hf
  have hgc : HasCompactSupport g := gantert_hasCompactSupport_physicalGenerator _ ω lam hc
  let g0 := compactTestGeneratorL2 hd ω hSmooth lam f hf hc
  have hg0 : (g0 : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] g :=
    (gantert_memLp_physicalGenerator hd _ ω hSmooth lam hf hc).coeFn_toLp
  have hPm : ∀ s t, P (s + t) = (P s).comp (P t) := by
    intro s t
    apply ContinuousLinearMap.ext
    exact kernelL2Action_add hd hΛ R s t
  exact dynkinOrbit_integral (dynkinAction_zero hd hΛ R) hPm
    (fun t u => R.kernelL2Action_norm_le hd hΛ t u)
    (gmp_compact_test_strong_generator hd hΛ R hSmooth f hf hc f0 hrep)
    (dynkinOrbit_tendsto_of_generator
      (gmp_compact_test_strong_generator hd hΛ R hSmooth g hgf hgc g0 hg0)) T

private theorem dynkin_integrable_bounded {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {f : α → ℝ} (hf : Measurable f)
    (B : ℝ) (hB : ∀ x, ‖f x‖ ≤ B) : Integrable f μ :=
  ⟨hf.aestronglyMeasurable, HasFiniteIntegral.of_bounded (Eventually.of_forall hB)⟩

/-- Identify a time integral in L² by testing against finite-measure indicators.
The joint representative is measurable and bounded, so scalar Fubini applies locally. -/
private theorem dynkin_integral_representative
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]
    (u : ℝ → Lp ℝ 2 μ) (hu : Continuous u)
    (U : ℝ → α → ℝ) (hU : Measurable (Function.uncurry U))
    (B : ℝ) (hB : ∀ t x, ‖U t x‖ ≤ B)
    (hrep : ∀ t, (u t : α → ℝ) =ᵐ[μ] U t) (T : ℝ≥0) :
    ((∫ t in (0 : ℝ)..(T : ℝ), u t : Lp ℝ 2 μ) : α → ℝ) =ᵐ[μ]
      fun x => ∫ t in (0 : ℝ)..(T : ℝ), U t x := by
  let ν : Measure ℝ := volume.restrict (Ioc (0 : ℝ) T)
  have hprod (s : Set α) (hs : μ s < ∞) :
      Integrable (fun p : α × ℝ => U p.2 p.1) ((μ.restrict s).prod ν) := by
    letI : IsFiniteMeasure (μ.restrict s) := ⟨by simpa only [Measure.restrict_apply_univ] using hs⟩
    exact dynkin_integrable_bounded _ (hU.comp measurable_swap) B (fun p => hB _ _)
  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
  · intro s hs hμs
    exact integrableOn_Lp_of_measure_ne_top _ (by norm_num) hμs.ne
  · intro s hs hμs
    change Integrable (fun x => ∫ t in (0 : ℝ)..(T : ℝ), U t x) (μ.restrict s)
    simpa only [intervalIntegral.integral_of_le T.coe_nonneg, ν] using
      (hprod s hμs).integral_prod_left
  · intro s hs hμs
    let v : Lp ℝ 2 μ := indicatorConstLp 2 hs hμs.ne (1 : ℝ)
    calc
      _ = inner ℝ v (∫ t in (0 : ℝ)..(T : ℝ), u t) :=
        (L2.inner_indicatorConstLp_one hs hμs.ne _).symm
      _ = ∫ t in (0 : ℝ)..(T : ℝ), inner ℝ v (u t) :=
        ((innerSL ℝ v).intervalIntegral_comp_comm (hu.intervalIntegrable 0 T)).symm
      _ = ∫ t in (0 : ℝ)..(T : ℝ), ∫ x in s, U t x ∂μ := by
        apply intervalIntegral.integral_congr
        intro t ht
        change inner ℝ (indicatorConstLp 2 hs hμs.ne (1 : ℝ)) (u t) = ∫ x in s, U t x ∂μ
        rw [L2.inner_indicatorConstLp_one hs hμs.ne]
        exact integral_congr_ae (ae_restrict_of_ae (hrep t))
      _ = _ := by
        change (∫ t in (0 : ℝ)..(T : ℝ), ∫ x in s, U t x ∂μ) =
          ∫ x in s, (∫ t in (0 : ℝ)..(T : ℝ), U t x) ∂μ
        simp_rw [intervalIntegral.integral_of_le T.coe_nonneg]
        exact (integral_integral_swap (hprod s hμs)).symm

section Actual
variable {d : ℕ} (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    {ω : FieldPair d} {hω : IsRegular Λ ω} {lam : ℝ}
    {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (R : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)

private theorem dynkin_transition_bound (f : Vec d →ᵇ ℝ) (t : ℝ≥0) (x : Vec d) :
    ‖∫ y, f y ∂R.transitionKernel t x‖ ≤ ‖f‖ := by
  letI := R.transitionKernel_isMarkovKernel t
  simpa only [probReal_univ, mul_one] using
    (norm_integral_le_of_norm_le_const (μ := R.transitionKernel t x)
      (Eventually.of_forall fun y => f.norm_coe_le_norm y))

private theorem dynkin_transition_measurable (f : Vec d →ᵇ ℝ) :
    Measurable (fun p : ℝ × Vec d => ∫ y, f y ∂R.transitionKernel p.1.toNNReal p.2) := by
  change Measurable (Function.uncurry (fun t : ℝ => fun x : Vec d =>
    ∫ y, f y ∂R.transitionKernel t.toNNReal x))
  apply measurable_uncurry_of_continuous_of_measurable
  · intro x
    exact (gantert_continuous_transition_time hd Λ hΛ ω hω lam h0 h1 R f x).comp
      continuous_real_toNNReal
  · intro t
    exact f.continuous.stronglyMeasurable.integral_kernel.measurable

private theorem dynkin_action_representative (f : Vec d → ℝ)
    (f0 : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hrep : (f0 : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] f) (t : ℝ≥0) :
    (R.kernelL2Action hd hΛ t f0 : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam]
      fun x => ∫ y, f y ∂R.transitionKernel t x := by
  letI : SigmaFinite (physicalReversibleMeasure ω hd lam) :=
    EinsteinRelation.Diffusion.physicalReversibleMeasure_sigmaFinite hd ω lam
  letI := R.transitionKernel_isMarkovKernel t
  exact (WeightedKernelL2.kernelIntegralL2_coe (R.transitionKernel_invariant hd hΛ t) f0).trans
    (WeightedKernelL2.kernelIntegral_ae_congr (R.transitionKernel_invariant hd hΛ t) hrep)

private theorem dynkin_compact_orbit_continuous (hSmooth : IsSmoothFieldPair ω)
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (f0 : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hrep : (f0 : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] f) :
    Continuous (fun t => R.kernelL2Action hd hΛ t f0) := by
  let P := dynkinActionCLM hd hΛ R
  have hPm : ∀ s t, P (s + t) = (P s).comp (P t) := by
    intro s t
    apply ContinuousLinearMap.ext
    exact kernelL2Action_add hd hΛ R s t
  exact dynkinOrbit_continuous (dynkinAction_zero hd hΛ R) hPm
    (fun t u => R.kernelL2Action_norm_le hd hΛ t u) f0
    (dynkinOrbit_tendsto_of_generator
      (gmp_compact_test_strong_generator hd hΛ R hSmooth f hf hc f0 hrep))

/-- The literal transition residual vanishes at almost every physical start. -/
theorem gmp_compact_test_evolution_ae (hSmooth : IsSmoothFieldPair ω)
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (T : ℝ≥0) :
    (fun x => (∫ y, f y ∂R.transitionKernel T x) - f x) =ᵐ[physicalReversibleMeasure ω hd lam]
      fun x => ∫ t in (0 : ℝ)..(T : ℝ),
        ∫ y, physicalGenerator (firstCoordinateIndex hd) ω lam f y
          ∂R.transitionKernel t.toNNReal x := by
  letI := gantert_physicalMeasure_locallyFinite hd ω lam
  letI : SigmaFinite (physicalReversibleMeasure ω hd lam) :=
    EinsteinRelation.Diffusion.physicalReversibleMeasure_sigmaFinite hd ω lam
  have hfm : MemLp f 2 (physicalReversibleMeasure ω hd lam) :=
    hf.continuous.memLp_of_hasCompactSupport hc
  let f0 := hfm.toLp f
  let g := physicalGenerator (firstCoordinateIndex hd) ω lam f
  have hgf : ContDiff ℝ (⊤ : ℕ∞) g :=
    gantert_contDiff_physicalGenerator _ ω hSmooth lam hf
  have hgc : HasCompactSupport g := gantert_hasCompactSupport_physicalGenerator _ ω lam hc
  let g0 := compactTestGeneratorL2 hd ω hSmooth lam f hf hc
  have hg0 : (g0 : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] g :=
    (gantert_memLp_physicalGenerator hd _ ω hSmooth lam hf hc).coeFn_toLp
  let gB := gantertCompactObservable g hgf.continuous hgc
  have he := gmp_compact_test_integrated_evolution hd hΛ R hSmooth f hf hc f0 hfm.coeFn_toLp T
  have hcont := (dynkin_compact_orbit_continuous hd hΛ R hSmooth g hgf hgc g0 hg0).comp
    continuous_real_toNNReal
  have hi := dynkin_integral_representative (physicalReversibleMeasure ω hd lam)
    (fun t : ℝ => R.kernelL2Action hd hΛ t.toNNReal g0) hcont
    (fun t x => ∫ y, gB y ∂R.transitionKernel t.toNNReal x)
    (dynkin_transition_measurable hd hΛ R gB) ‖gB‖
    (fun t x => dynkin_transition_bound hd hΛ R gB t.toNNReal x)
    (fun t => dynkin_action_representative hd hΛ R g g0 hg0 t.toNNReal) T
  rw [← he] at hi
  filter_upwards [hi, Lp.coeFn_sub (R.kernelL2Action hd hΛ T f0) f0,
    dynkin_action_representative hd hΛ R f f0 hfm.coeFn_toLp T, hfm.coeFn_toLp]
    with x hix hs hx hf0
  change (∫ y, f y ∂R.transitionKernel T x) - f x = _
  rw [hs, Pi.sub_apply, hx, hf0] at hix
  exact hix

private theorem dynkin_transition_add (f : Vec d →ᵇ ℝ) (s t : ℝ≥0) (x : Vec d) :
    (∫ y, f y ∂R.transitionKernel (s + t) x) =
      ∫ z, (∫ y, f y ∂R.transitionKernel t z) ∂R.transitionKernel s x := by
  letI := R.transitionKernel_isMarkovKernel s
  letI := R.transitionKernel_isMarkovKernel t
  rw [R.transitionKernel_add s t]
  exact Kernel.integral_comp
    (dynkin_integrable_bounded _ f.continuous.measurable ‖f‖ (fun y => f.norm_coe_le_norm y))

/-- Smoothing an exceptional set by a positive transition and taking the time-zero
limit upgrades a bounded continuous evolution identity to every starting point. -/
private theorem dynkin_evolution_every_start
    (f g : Vec d →ᵇ ℝ) (T : ℝ≥0)
    (hae : (fun x => (∫ y, f y ∂R.transitionKernel T x) - f x)
      =ᵐ[physicalReversibleMeasure ω hd lam]
        fun x => ∫ t in (0 : ℝ)..(T : ℝ), ∫ y, g y ∂R.transitionKernel t.toNNReal x)
    (x : Vec d) :
    (∫ y, f y ∂R.transitionKernel T x) - f x =
      ∫ t in (0 : ℝ)..(T : ℝ), ∫ y, g y ∂R.transitionKernel t.toNNReal x := by
  let ν : Measure ℝ := volume.restrict (Ioc (0 : ℝ) T)
  have he (ε : ℝ≥0) (hε : 0 < ε) :
      (∫ y, f y ∂R.transitionKernel (ε + T) x) -
        (∫ y, f y ∂R.transitionKernel ε x) =
      ∫ t in (0 : ℝ)..(T : ℝ), ∫ y, g y ∂R.transitionKernel (ε + t.toNNReal) x := by
    letI := R.transitionKernel_isMarkovKernel ε
    letI := R.transitionKernel_isMarkovKernel T
    have hfi : Integrable (fun z => ∫ y, f y ∂R.transitionKernel T z)
        (R.transitionKernel ε x) :=
      dynkin_integrable_bounded _ f.continuous.stronglyMeasurable.integral_kernel.measurable
        ‖f‖ (fun z => dynkin_transition_bound hd hΛ R f T z)
    have hf0 : Integrable f (R.transitionKernel ε x) :=
      dynkin_integrable_bounded _ f.continuous.measurable ‖f‖ (fun y => f.norm_coe_le_norm y)
    have h := integral_congr_ae
      ((gantert_transition_absolutelyContinuous hd Λ hΛ ω hω lam h0 h1 R ε hε x).ae_le hae)
    rw [integral_sub hfi hf0, ← dynkin_transition_add hd hΛ R f ε T x] at h
    rw [h]
    have hi : Integrable
        (fun p : Vec d × ℝ => ∫ y, g y ∂R.transitionKernel p.2.toNNReal p.1)
        ((R.transitionKernel ε x).prod ν) :=
      dynkin_integrable_bounded _ ((dynkin_transition_measurable hd hΛ R g).comp measurable_swap)
        ‖g‖ (fun p => dynkin_transition_bound hd hΛ R g p.2.toNNReal p.1)
    calc
      _ = ∫ t in (0 : ℝ)..(T : ℝ),
          ∫ z, (∫ y, g y ∂R.transitionKernel t.toNNReal z) ∂R.transitionKernel ε x := by
        change (∫ z, (∫ t in (0 : ℝ)..(T : ℝ),
          ∫ y, g y ∂R.transitionKernel t.toNNReal z) ∂R.transitionKernel ε x) = _
        simp_rw [intervalIntegral.integral_of_le T.coe_nonneg]
        exact integral_integral_swap hi
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro t ht
        exact (dynkin_transition_add hd hΛ R g ε t.toNNReal x).symm
  have hfcont := gantert_continuous_transition_time hd Λ hΛ ω hω lam h0 h1 R f x
  have hgcont := gantert_continuous_transition_time hd Λ hΛ ω hω lam h0 h1 R g x
  have heps : Tendsto (fun ε : ℝ≥0 => ε) (𝓝[>] (0 : ℝ≥0)) (𝓝 (0 : ℝ≥0)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hfT : Tendsto (fun ε : ℝ≥0 => ∫ y, f y ∂R.transitionKernel (ε + T) x)
      (𝓝[>] (0 : ℝ≥0)) (𝓝 (∫ y, f y ∂R.transitionKernel T x)) := by
    simpa only [Function.comp_def, zero_add] using (hfcont.tendsto (0 + T)).comp (heps.add_const T)
  have hfzero : Tendsto (fun ε : ℝ≥0 => ∫ y, f y ∂R.transitionKernel ε x)
      (𝓝[>] (0 : ℝ≥0)) (𝓝 (f x)) :=
    (gantert_transition_tendsto_zero hd Λ hΛ ω hω lam h0 h1 R f x).mono_left
      nhdsWithin_le_nhds
  have hint : Tendsto (fun ε : ℝ≥0 =>
      ∫ t in (0 : ℝ)..(T : ℝ), ∫ y, g y ∂R.transitionKernel (ε + t.toNNReal) x)
      (𝓝[>] (0 : ℝ≥0))
      (𝓝 (∫ t in (0 : ℝ)..(T : ℝ), ∫ y, g y ∂R.transitionKernel t.toNNReal x)) := by
    simp_rw [intervalIntegral.integral_of_le T.coe_nonneg]
    apply tendsto_integral_filter_of_dominated_convergence (μ := ν) (fun _ => ‖g‖)
    · exact Eventually.of_forall fun ε =>
        (hgcont.comp (continuous_const.add continuous_real_toNNReal)).aestronglyMeasurable
    · exact Eventually.of_forall fun ε => Eventually.of_forall fun t =>
        dynkin_transition_bound hd hΛ R g (ε + t.toNNReal) x
    · exact integrable_const _
    · exact Eventually.of_forall fun t => by
        simpa only [Function.comp_def, zero_add] using (hgcont.tendsto (0 + t.toNNReal)).comp (heps.add_const t.toNNReal)
  apply tendsto_nhds_unique (hfT.sub hfzero)
  apply hint.congr'
  filter_upwards [eventually_mem_nhdsWithin] with ε hε
  exact (he ε hε).symm

/-- The actual supplied law has zero compensated compact-test mean at every start. -/
theorem gmp_actual_compensated_test_mean_zero :
∀ {d : ℕ} (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 ≤ Λ)
  {ω : FieldPair d} {hω : IsRegular Λ ω} {lam : ℝ}
  {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
  (R : EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization
    hd Λ hΛ ω hω lam h0 h1) (hSmooth : IsSmoothFieldPair ω)
  (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
  (x : Vec d) (T : ℝ≥0),
  (∫ γ, compensatedTest (physicalGenerator (firstCoordinateIndex hd) ω lam) f T γ
    ∂R.pathLaw x) = 0 := by
  intro d hd Λ hΛ ω hω lam h0 h1 R hSmooth f hf hc x T
  let fB := gantertCompactObservable f hf.continuous hc
  let g := physicalGenerator (firstCoordinateIndex hd) ω lam f
  let gB := gantertCompactObservable g
    (gantert_contDiff_physicalGenerator _ ω hSmooth lam hf).continuous
    (gantert_hasCompactSupport_physicalGenerator _ ω lam hc)
  have he := dynkin_evolution_every_start hd hΛ R fB gB T
    (gmp_compact_test_evolution_ae hd hΛ R hSmooth f hf hc T) x
  rw [gantert_integral_compensatedTest hd Λ hΛ ω hω lam h0 h1 R hSmooth f hf hc x T]
  exact sub_eq_zero.mpr he

end Actual
end EinsteinFull.Blueprint
