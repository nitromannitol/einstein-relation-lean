import EinsteinFull.Work.W1.SpatialMollificationRepresentativeSupport
import EinsteinFull.Calculus.PhysicalH1ClosedGraphSupport
import EinsteinRelation.Correctors.LocalWeakGradientUniqueness
import EinsteinRelation.Correctors.SpatialWeakCongruence
import EinsteinRelation.Calculus.ClassicalSpatialDerivative
import EinsteinRelation.Correctors.SpatialWeakLocalization

/-! Compact support and weight comparisons for actual physical H1 mollification.
The gradient support is derived from local distributional uniqueness off the
compact set. All comparisons use the literal exponential physical measure.
-/

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace EinsteinFull
open EinsteinRelation
noncomputable section
variable {d : ℕ}

/-- A genuine weak derivative vanishes off every closed AE support of its value. -/
theorem weakPartialDerivative_zero_off_closed {K : Set (Vec d)} (hK : IsClosed K)
    {f g : Vec d → ℝ} {j : Fin d}
    (hfg : HasWeakPartialDerivative univ j f g)
    (hf : ∀ᵐ x ∂volume, x ∉ K → f x = 0) :
    ∀ᵐ x ∂volume, x ∉ K → g x = 0 := by
  have hf0 : f =ᵐ[volume.restrict Kᶜ] (fun _ => 0) :=
    (ae_restrict_iff' hK.measurableSet.compl).mpr hf
  have hlocal := Correctors.hasWeakPartialDerivative_mono (subset_univ Kᶜ) hfg
  have hzero : HasWeakPartialDerivative Kᶜ j (fun _ => 0) (fun _ => 0) := by
    refine ⟨locallyIntegrableOn_zero, locallyIntegrableOn_zero, ?_⟩
    intro φ _
    simp only [zero_mul, integral_zero, neg_zero]
  have hlocal0 := Correctors.hasWeakPartialDerivative_congr_ae hK.isOpen_compl
    hlocal hf0 (EventuallyEq.refl _ _)
  exact (ae_restrict_iff' hK.measurableSet.compl).mp
    (Correctors.weakPartialDerivative_ae_eq_on_open hK.isOpen_compl hlocal0 hzero)

/-- The actual complex H1 graph derives gradient support from value support;
no gradient-support premise is required. -/
theorem physicalH1Graph_gradient_zero_off_closed (m : Measure (Vec d))
    (hm : m = volume ∨ ∃ (i : Fin d) (lam : ℝ), m = physicalForceMeasure i lam)
    (u : Lp ℂ 2 m) (G : Fin d → Lp ℂ 2 m)
    (hu : IsPhysicalH1Graph m hm u G) {K : Set (Vec d)} (hK : IsClosed K)
    (huK : ∀ᵐ x ∂m, x ∉ K → u x = 0) :
    ∀ j, ∀ᵐ x ∂m, x ∉ K → G j x = 0 := by
  have hvm : (volume : Measure (Vec d)) ≪ m := by
    rcases hm with rfl | ⟨i, lam, rfl⟩
    · exact Measure.AbsolutelyContinuous.rfl
    · exact volume_absolutelyContinuous_physicalForceMeasure i lam
  have hmv : m ≪ (volume : Measure (Vec d)) := by
    rcases hm with rfl | ⟨i, lam, rfl⟩
    · exact Measure.AbsolutelyContinuous.rfl
    · exact physicalForceMeasure_absolutelyContinuous i lam
  have hr : ∀ᵐ x ∂volume, x ∉ K → (u x).re = 0 := by
    filter_upwards [hvm.ae_le huK] with x hx hxK
    rw [hx hxK, Complex.zero_re]
  have hi : ∀ᵐ x ∂volume, x ∉ K → (u x).im = 0 := by
    filter_upwards [hvm.ae_le huK] with x hx hxK
    rw [hx hxK, Complex.zero_im]
  intro j
  filter_upwards [hmv.ae_le (weakPartialDerivative_zero_off_closed hK (hu.1 j) hr),
    hmv.ae_le (weakPartialDerivative_zero_off_closed hK (hu.2 j) hi)] with x hx hy hxK
  exact Complex.ext (hx hxK) (hy hxK)

/-- Both signs of the physical force have positive finite density bounds on
any compact set; the witnesses depend only on that set and the force. -/
theorem physicalForceDensity_compact_bounds (i : Fin d) (lam : ℝ)
    {K : Set (Vec d)} (hK : IsCompact K) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ x ∈ K, c ≤ Real.exp (2 * lam * x i) ∧ Real.exp (2 * lam * x i) ≤ C := by
  have hc : Continuous (fun x : Vec d => Real.exp (2 * lam * x i)) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_apply i))
  obtain ⟨c, hcpos, hclower⟩ := hK.exists_forall_le' hc.continuousOn (fun _ _ => Real.exp_pos _)
  obtain ⟨B, hB⟩ := hK.bddAbove_image hc.continuousOn
  refine ⟨c, max B 1, hcpos, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro x hx
  exact ⟨hclower x hx, (hB (mem_image_of_mem _ hx)).trans (le_max_left _ _)⟩

/-- Literal restricted-measure comparisons, with one pair of witnesses before
all measurable subsets and functions. -/
theorem physicalForceMeasure_compact_comparison (i : Fin d) (lam : ℝ)
    {K : Set (Vec d)} (hK : IsCompact K) :
    ∃ c C : ℝ≥0, 0 < c ∧ 0 < C ∧
      (c : ℝ≥0∞) • volume.restrict K ≤ (physicalForceMeasure i lam).restrict K ∧
      (physicalForceMeasure i lam).restrict K ≤ (C : ℝ≥0∞) • volume.restrict K := by
  obtain ⟨c, C, hc, hC, hb⟩ := physicalForceDensity_compact_bounds i lam hK
  refine ⟨⟨c, hc.le⟩, ⟨C, hC.le⟩, hc, hC, ?_, ?_⟩
  · rw [physicalForceMeasure, restrict_withDensity hK.measurableSet,
      ← withDensity_const]
    apply withDensity_mono
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    simpa only [ENNReal.ofReal_eq_coe_nnreal hc.le] using!
      ENNReal.ofReal_le_ofReal (hb x hx).1
  · rw [physicalForceMeasure, restrict_withDensity hK.measurableSet,
      ← withDensity_const]
    apply withDensity_mono
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    simpa only [ENNReal.ofReal_eq_coe_nnreal hC.le] using!
      ENNReal.ofReal_le_ofReal (hb x hx).2

/-- An AE-supported function has exactly its restricted seminorm. -/
theorem eLpNorm_eq_restrict_of_ae_zero_off {E : Type*} [NormedAddCommGroup E]
    (m : Measure (Vec d)) {K : Set (Vec d)} (hK : MeasurableSet K)
    {f : Vec d → E} (hfK : ∀ᵐ x ∂m, x ∉ K → f x = 0) (p : ℝ≥0∞) :
    eLpNorm f p m = eLpNorm f p (m.restrict K) := by
  have heq : K.indicator f =ᵐ[m] f := by
    filter_upwards [hfK] with x hx
    by_cases h : x ∈ K
    · simp only [indicator_of_mem h]
    · simp only [indicator_of_notMem h, hx h]
  exact (eLpNorm_congr_ae heq).symm.trans (eLpNorm_indicator_eq_eLpNorm_restrict hK)

/-- Compact support transfers literal L2 membership in both directions. -/
theorem memLp_physicalForceMeasure_iff_of_ae_zero_off_compact
    {E : Type*} [NormedAddCommGroup E] (i : Fin d) (lam : ℝ)
    {K : Set (Vec d)} (hK : IsCompact K) {f : Vec d → E}
    (hfK : ∀ᵐ x ∂volume, x ∉ K → f x = 0) :
    MemLp f 2 (physicalForceMeasure i lam) ↔ MemLp f 2 volume := by
  have hfKm := (physicalForceMeasure_absolutelyContinuous i lam).ae_le hfK
  have heq (m : Measure (Vec d)) (hm : ∀ᵐ x ∂m, x ∉ K → f x = 0) :
      K.indicator f =ᵐ[m] f := by
    filter_upwards [hm] with x hx
    by_cases h : x ∈ K
    · simp only [indicator_of_mem h]
    · simp only [indicator_of_notMem h, hx h]
  have hmem (m : Measure (Vec d)) (hm : ∀ᵐ x ∂m, x ∉ K → f x = 0) :
      MemLp f 2 m ↔ MemLp f 2 (m.restrict K) := by
    rw [← memLp_indicator_iff_restrict hK.measurableSet]
    exact memLp_congr_ae (heq m hm).symm
  rw [hmem _ hfKm, hmem _ hfK]
  obtain ⟨c, C, hc, _, hlo, hhi⟩ := physicalForceMeasure_compact_comparison i lam hK
  have hc0 : (c : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr (ne_of_gt hc)
  have hreverse : volume.restrict K ≤
      (c : ℝ≥0∞)⁻¹ • (physicalForceMeasure i lam).restrict K := by
    apply Measure.le_iff.mpr
    intro S hS
    have h := mul_le_mul_right (Measure.le_iff.mp hlo S hS) (c : ℝ≥0∞)⁻¹
    simpa only [Measure.smul_apply, smul_eq_mul, ← mul_assoc,
      ENNReal.inv_mul_cancel hc0 ENNReal.coe_ne_top, one_mul] using h
  exact ⟨fun hf => hf.of_measure_le_smul (by simp [hc0]) hreverse,
    fun hf => hf.of_measure_le_smul ENNReal.coe_ne_top hhi⟩

/-- The value and all actual Euclidean coordinate derivatives of a compactly
supported physical graph are genuine Lebesgue L2 functions. -/
theorem physicalH1Graph_memLp_volume_of_ae_zero_off_compact
    (i : Fin d) (lam : ℝ) (u : Lp ℂ 2 (physicalForceMeasure i lam))
    (G : Fin d → Lp ℂ 2 (physicalForceMeasure i lam))
    (hu : IsPhysicalH1Graph (physicalForceMeasure i lam) (Or.inr ⟨i, lam, rfl⟩) u G)
    {K : Set (Vec d)} (hK : IsCompact K)
    (huK : ∀ᵐ x ∂physicalForceMeasure i lam, x ∉ K → u x = 0) :
    MemLp u 2 volume ∧ ∀ j, MemLp (G j) 2 volume := by
  have hvol := volume_absolutelyContinuous_physicalForceMeasure i lam
  have hGK := physicalH1Graph_gradient_zero_off_closed _ _ u G hu hK.isClosed huK
  exact ⟨(memLp_physicalForceMeasure_iff_of_ae_zero_off_compact i lam hK
      (hvol.ae_le huK)).mp (Lp.memLp u),
    fun j => (memLp_physicalForceMeasure_iff_of_ae_zero_off_compact i lam hK
      (hvol.ae_le (hGK j))).mp (Lp.memLp (G j))⟩

/-- One finite constant compares physical and Lebesgue L2 seminorms for every
function supported in the chosen compact set. -/
theorem eLpNorm_physicalForceMeasure_le_on_compact (i : Fin d) (lam : ℝ)
    {K : Set (Vec d)} (hK : IsCompact K) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ {E : Type*} [NormedAddCommGroup E] (f : Vec d → E),
      (∀ᵐ x ∂volume, x ∉ K → f x = 0) →
      eLpNorm f 2 (physicalForceMeasure i lam) ≤ C * eLpNorm f 2 volume := by
  obtain ⟨_, C, _, _, _, hhi⟩ := physicalForceMeasure_compact_comparison i lam hK
  refine ⟨(C : ℝ≥0∞) ^ (1 / (2 : ℝ)), by finiteness, ?_⟩
  intro E _ f hf
  rw [eLpNorm_eq_restrict_of_ae_zero_off _ hK.measurableSet
    ((physicalForceMeasure_absolutelyContinuous i lam).ae_le hf)]
  calc
    _ ≤ eLpNorm f 2 ((C : ℝ≥0∞) • volume.restrict K) := eLpNorm_mono_measure f hhi
    _ = (C : ℝ≥0∞) ^ (1 / (2 : ℝ)) * eLpNorm f 2 (volume.restrict K) := by
      rw [eLpNorm_smul_measure_of_ne_zero_of_ne_top (by norm_num) (by norm_num)]
      norm_num [smul_eq_mul]
    _ = _ := by rw [← eLpNorm_eq_restrict_of_ae_zero_off _ hK.measurableSet hf]

/-- A single compact envelope for all scales in [-1,1], also containing the
original compact set. This is topological support control, not a norm change. -/
def spatialMollifyCompactEnvelope (K : Set (Vec d)) : Set (Vec d) :=
  K ∪ (fun p : ℝ × (Vec d × Vec d) => p.2.1 - p.1 • p.2.2) ''
    (Icc (-1 : ℝ) 1 ×ˢ (K ×ˢ tsupport (mollifier d)))

theorem isCompact_spatialMollifyCompactEnvelope {K : Set (Vec d)} (hK : IsCompact K) :
    IsCompact (spatialMollifyCompactEnvelope K) :=
  hK.union ((isCompact_Icc.prod (hK.prod (hasCompactSupport_mollifier d))).image
    (continuous_snd.fst.sub (continuous_fst.smul continuous_snd.snd)))

theorem spatialMollifySupport_subset_compactEnvelope {K : Set (Vec d)} {ε : ℝ}
    (hε : ε ∈ Icc (-1 : ℝ) 1) :
    spatialMollifySupport K ε ⊆ spatialMollifyCompactEnvelope K := by
  rintro x ⟨p, hp, rfl⟩
  exact Or.inr ⟨(ε, p), ⟨hε, hp⟩, rfl⟩

/-- Strong Lebesgue L2 convergence with one compact AE support transfers to
literal physical L2 convergence. This estimate is used on actual mollifiers. -/
theorem tendsto_eLpNorm_physicalForceMeasure_of_compact_support
    {E : Type*} [NormedAddCommGroup E] {α : Type*} {l : Filter α}
    (i : Fin d) (lam : ℝ) {K : Set (Vec d)} (hK : IsCompact K)
    (f : α → Vec d → E) (hfK : ∀ᶠ a in l, ∀ᵐ x ∂volume, x ∉ K → f a x = 0)
    (hf : Tendsto (fun a => eLpNorm (f a) 2 volume) l (𝓝 0)) :
    Tendsto (fun a => eLpNorm (f a) 2 (physicalForceMeasure i lam)) l (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := eLpNorm_physicalForceMeasure_le_on_compact i lam hK
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa only [mul_zero] using ENNReal.Tendsto.const_mul hf (Or.inr hC))
    (Eventually.of_forall fun _ => zero_le)
  exact hfK.mono fun a ha => hbound (f a) ha

/-- The actual pointwise smooth mollification of compactly supported data
converges in the physical measure for arbitrary signed force. -/
theorem tendsto_eLpNorm_spatialSmoothMollify_physicalForceMeasure
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (i : Fin d) (lam : ℝ) (f : Lp E 2 (volume : Measure (Vec d)))
    {K : Set (Vec d)} (hK : IsCompact K)
    (hfK : ∀ᵐ x ∂volume, x ∉ K → f x = 0) :
    Tendsto (fun ε : {ε : ℝ // 0 < ε} =>
      eLpNorm (spatialSmoothMollify ε f - (f : Vec d → E)) 2 (physicalForceMeasure i lam))
      (comap Subtype.val (𝓝 0)) (𝓝 0) := by
  have hfint := integrable_L2_of_ae_zero_off_compact f hK hfK
  have hv := tendsto_toLp_spatialSmoothMollify_zero f hfint
  have hvnorm : Tendsto (fun ε : {ε : ℝ // 0 < ε} =>
      eLpNorm (spatialSmoothMollify ε f - (f : Vec d → E)) 2 volume)
      (comap Subtype.val (𝓝 0)) (𝓝 0) := by
    have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ f).mp hv
    apply ht.congr
    intro ε
    apply eLpNorm_congr_ae
    exact (MemLp.coeFn_toLp (memLp_spatialSmoothMollify ε.property f hfint)).sub
      EventuallyEq.rfl
  apply tendsto_eLpNorm_physicalForceMeasure_of_compact_support i lam
    (isCompact_spatialMollifyCompactEnvelope hK) _ ?_ hvnorm
  have hs : ∀ᶠ ε : {ε : ℝ // 0 < ε} in comap Subtype.val (𝓝 0),
      (ε : ℝ) ∈ Icc (-1 : ℝ) 1 :=
    tendsto_comap.eventually (Icc_mem_nhds (by norm_num) (by norm_num))
  filter_upwards [hs] with ε hε
  filter_upwards [hfK] with x hx hxE
  have hxK : x ∉ K := fun h => hxE (Or.inl h)
  have hxS : x ∉ spatialMollifySupport K ε :=
    fun h => hxE (spatialMollifySupport_subset_compactEnvelope hε h)
  simp only [Pi.sub_apply, spatialSmoothMollify_zero_off ε.property.ne' hfK hxS,
    hx hxK, sub_zero]

/-- Real linear value maps commute with the literal pointwise smooth average. -/
theorem spatialSmoothMollify_compCLM {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (A : E →L[ℝ] F) {ε : ℝ} (hε : ε ≠ 0) {f : Vec d → E}
    (hf : LocallyIntegrable f volume) :
    spatialSmoothMollify ε (fun x => A (f x)) = fun x => A (spatialSmoothMollify ε f x) := by
  rw [spatialSmoothMollify_eq_convolution, spatialSmoothMollify_eq_convolution]
  funext x
  have hc := (hasCompactSupport_spatialScaledKernel (d := d) hε).comp_homeomorph
    (Homeomorph.neg (Vec d))
  have hd := (contDiff_spatialScaledKernel (d := d) ε).comp contDiff_neg
  have hi := hc.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) hd.continuous hf x
  simp only [convolution_def]
  simpa only [ContinuousLinearMap.lsmul_apply, Function.comp_apply,
    map_smul] using! A.integral_comp_comm hi

/-- Compact AE support supplies physical L2 membership of the actual smooth
average at every positive scale, without a global weight bound. -/
theorem memLp_spatialSmoothMollify_physicalForceMeasure_of_memLp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (i : Fin d) (lam : ℝ) {f : Vec d → E} (hf : MemLp f 2 volume)
    {K : Set (Vec d)} (hK : IsCompact K)
    (hfK : ∀ᵐ x ∂volume, x ∉ K → f x = 0) {ε : ℝ} (hε : 0 < ε) :
    MemLp (spatialSmoothMollify ε f) 2 (physicalForceMeasure i lam) := by
  have hrep := hf.coeFn_toLp
  have hsupport : ∀ᵐ x ∂volume, x ∉ K → hf.toLp f x = 0 := by
    filter_upwards [hrep, hfK] with x hx hy hKx
    exact hx.trans (hy hKx)
  have hint := integrable_L2_of_ae_zero_off_compact (hf.toLp f) hK hsupport
  have hmem := memLp_spatialSmoothMollify hε (hf.toLp f) hint
  rw [spatialSmoothMollify_congr_ae ε hrep] at hmem
  apply (memLp_physicalForceMeasure_iff_of_ae_zero_off_compact i lam
    (isCompact_spatialMollifySupport hK ε) ?_).mpr hmem
  exact ae_of_all _ fun _ hx => spatialSmoothMollify_zero_off hε.ne' hfK hx

/-- The weighted approximation theorem applies directly to actual functions,
so no representative chosen by a change of measure appears in its conclusion. -/
theorem tendsto_eLpNorm_spatialSmoothMollify_physicalForceMeasure_of_memLp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (i : Fin d) (lam : ℝ) {f : Vec d → E} (hf : MemLp f 2 volume)
    {K : Set (Vec d)} (hK : IsCompact K)
    (hfK : ∀ᵐ x ∂volume, x ∉ K → f x = 0) :
    Tendsto (fun ε : {ε : ℝ // 0 < ε} =>
      eLpNorm (spatialSmoothMollify ε f - f) 2 (physicalForceMeasure i lam))
      (comap Subtype.val (𝓝 0)) (𝓝 0) := by
  have hrep := hf.coeFn_toLp
  have hs : ∀ᵐ x ∂volume, x ∉ K → hf.toLp f x = 0 := by
    filter_upwards [hrep, hfK] with x hx hy hxK
    exact hx.trans (hy hxK)
  have ht := tendsto_eLpNorm_spatialSmoothMollify_physicalForceMeasure i lam (hf.toLp f) hK hs
  apply ht.congr
  intro ε
  rw [spatialSmoothMollify_congr_ae ε hrep]
  apply eLpNorm_congr_ae
  exact EventuallyEq.rfl.sub ((physicalForceMeasure_absolutelyContinuous i lam).ae_eq hrep)

/-- Mollification preserves the literal complex physical H1 weak equations.
The displayed smooth derivative is constructed from the actual graph gradient. -/
theorem physicalH1Graph_spatialSmoothMollify_weak_equations
    (i : Fin d) (lam : ℝ) (u : Lp ℂ 2 (physicalForceMeasure i lam))
    (G : Fin d → Lp ℂ 2 (physicalForceMeasure i lam))
    (hu : IsPhysicalH1Graph (physicalForceMeasure i lam) (Or.inr ⟨i, lam, rfl⟩) u G)
    {K : Set (Vec d)} (hK : IsCompact K)
    (huK : ∀ᵐ x ∂physicalForceMeasure i lam, x ∉ K → u x = 0)
    {ε : ℝ} (hε : ε ≠ 0) :
    (∀ j, HasWeakPartialDerivative univ j
      (fun x => (spatialSmoothMollify ε u x).re)
      (fun x => (spatialSmoothMollify ε (G j) x).re)) ∧
    (∀ j, HasWeakPartialDerivative univ j
      (fun x => (spatialSmoothMollify ε u x).im)
      (fun x => (spatialSmoothMollify ε (G j) x).im)) := by
  have hmem := physicalH1Graph_memLp_volume_of_ae_zero_off_compact i lam u G hu hK huK
  have huloc := hmem.1.locallyIntegrable (by norm_num)
  have hGloc (j) := (hmem.2 j).locallyIntegrable (by norm_num)
  have hre := spatialSmoothMollify_compCLM Complex.reCLM hε huloc
  have him := spatialSmoothMollify_compCLM Complex.imCLM hε huloc
  change spatialSmoothMollify ε (fun x => (u x).re) = _ at hre
  change spatialSmoothMollify ε (fun x => (u x).im) = _ at him
  simp only [Complex.reCLM_apply] at hre
  simp only [Complex.imCLM_apply] at him
  constructor
  · intro j
    have hgr := spatialSmoothMollify_compCLM Complex.reCLM hε (hGloc j)
    simp only [Complex.reCLM_apply] at hgr
    rw [← hre, ← hgr]
    rw [← coordinateDerivative_spatialSmoothMollify hε (hu.1 j)]
    exact hasWeakPartialDerivative_of_contDiff j _
      ((contDiff_spatialSmoothMollify hε
        (hmem.1.re.locallyIntegrable (by norm_num))).of_le (by norm_num))
  · intro j
    have hgi := spatialSmoothMollify_compCLM Complex.imCLM hε (hGloc j)
    simp only [Complex.imCLM_apply] at hgi
    rw [← him, ← hgi]
    rw [← coordinateDerivative_spatialSmoothMollify hε (hu.2 j)]
    exact hasWeakPartialDerivative_of_contDiff j _
      ((contDiff_spatialSmoothMollify hε
        (hmem.1.im.locallyIntegrable (by norm_num))).of_le (by norm_num))

/-- Compact-interior approximation of the full actual physical H1 graph.
The error is the value L2 norm squared plus the sum of all coordinate L2 norm
squares, hence uses the Euclidean gradient energy rather than its Pi norm.
The approximants are the literal smooth spatial mollifications of the datum. -/
theorem exists_physicalH1Graph_compact_interior_mollification
    (i : Fin d) (lam : ℝ) (u : Lp ℂ 2 (physicalForceMeasure i lam))
    (G : Fin d → Lp ℂ 2 (physicalForceMeasure i lam))
    (hu : IsPhysicalH1Graph (physicalForceMeasure i lam) (Or.inr ⟨i, lam, rfl⟩) u G)
    {K U : Set (Vec d)} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (huK : ∀ᵐ x ∂physicalForceMeasure i lam, x ∉ K → u x = 0) :
    ∃ (v : {ε : ℝ // 0 < ε} → Lp ℂ 2 (physicalForceMeasure i lam))
      (H : {ε : ℝ // 0 < ε} → Fin d → Lp ℂ 2 (physicalForceMeasure i lam)),
      (∀ ε, IsPhysicalH1Graph (physicalForceMeasure i lam) (Or.inr ⟨i, lam, rfl⟩)
          (v ε) (H ε) ∧
        (v ε : Vec d → ℂ) =ᵐ[physicalForceMeasure i lam] spatialSmoothMollify ε u ∧
        (∀ j, (H ε j : Vec d → ℂ) =ᵐ[physicalForceMeasure i lam]
          spatialSmoothMollify ε (G j)) ∧
        ContDiff ℝ (⊤ : ℕ∞) (spatialSmoothMollify ε u) ∧
        HasCompactSupport (spatialSmoothMollify ε u)) ∧
      (∀ᶠ ε : {ε : ℝ // 0 < ε} in comap Subtype.val (𝓝 0),
        tsupport (spatialSmoothMollify ε u) ⊆ U) ∧
      Tendsto (fun ε => ‖v ε - u‖ ^ 2 + ∑ j : Fin d, ‖H ε j - G j‖ ^ 2)
        (comap Subtype.val (𝓝 0)) (𝓝 0) := by
  have hvol := volume_absolutelyContinuous_physicalForceMeasure i lam
  have huKv := hvol.ae_le huK
  have hGK := physicalH1Graph_gradient_zero_off_closed _ _ u G hu hK.isClosed huK
  have hGKv (j) := hvol.ae_le (hGK j)
  have hm := physicalH1Graph_memLp_volume_of_ae_zero_off_compact i lam u G hu hK huK
  have hv (ε : {ε : ℝ // 0 < ε}) :=
    memLp_spatialSmoothMollify_physicalForceMeasure_of_memLp i lam hm.1 hK huKv ε.property
  have hH (ε : {ε : ℝ // 0 < ε}) (j : Fin d) :=
    memLp_spatialSmoothMollify_physicalForceMeasure_of_memLp i lam (hm.2 j) hK
      (hGKv j) ε.property
  let v (ε : {ε : ℝ // 0 < ε}) := (hv ε).toLp (spatialSmoothMollify ε u)
  let H (ε : {ε : ℝ // 0 < ε}) (j : Fin d) :=
    (hH ε j).toLp (spatialSmoothMollify ε (G j))
  have hvr (ε) : (v ε : Vec d → ℂ) =ᵐ[physicalForceMeasure i lam]
      spatialSmoothMollify ε u := (hv ε).coeFn_toLp
  have hHr (ε) (j) : (H ε j : Vec d → ℂ) =ᵐ[physicalForceMeasure i lam]
      spatialSmoothMollify ε (G j) := (hH ε j).coeFn_toLp
  refine ⟨v, H, ?_, ?_, ?_⟩
  · intro ε
    refine ⟨?_, hvr ε, hHr ε,
      contDiff_spatialSmoothMollify ε.property.ne' (hm.1.locallyIntegrable (by norm_num)),
      hasCompactSupport_spatialSmoothMollify ε.property.ne' hK huKv⟩
    apply (isPhysicalH1Graph_iff_representatives _ _ (v ε) (H ε)
      _ _ (hvr ε) (hHr ε)).mpr
    exact physicalH1Graph_spatialSmoothMollify_weak_equations i lam u G hu hK huK ε.property.ne'
  · filter_upwards [tendsto_comap.eventually (eventually_spatialMollifySupport_subset hK hU hKU)]
      with ε hε
    exact (tsupport_spatialSmoothMollify_subset ε.property.ne' hK huKv).trans hε
  · have hvlim : Tendsto v (comap Subtype.val (𝓝 0)) (𝓝 u) := by
      apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' v u).mpr
      apply (tendsto_eLpNorm_spatialSmoothMollify_physicalForceMeasure_of_memLp
        i lam hm.1 hK huKv).congr
      intro ε
      exact (eLpNorm_congr_ae ((hvr ε).sub EventuallyEq.rfl)).symm
    have hHlim (j) : Tendsto (fun ε => H ε j) (comap Subtype.val (𝓝 0)) (𝓝 (G j)) := by
      apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' (fun ε => H ε j) (G j)).mpr
      apply (tendsto_eLpNorm_spatialSmoothMollify_physicalForceMeasure_of_memLp
        i lam (hm.2 j) hK (hGKv j)).congr
      intro ε
      exact (eLpNorm_congr_ae ((hHr ε j).sub EventuallyEq.rfl)).symm
    have hpair := hvlim.prodMk_nhds (tendsto_pi_nhds.mpr hHlim)
    have hc : Continuous (fun p : Lp ℂ 2 (physicalForceMeasure i lam) ×
        (Fin d → Lp ℂ 2 (physicalForceMeasure i lam)) =>
        ‖p.1 - u‖ ^ 2 + ∑ j : Fin d, ‖p.2 j - G j‖ ^ 2) := by
      fun_prop
    simpa only [sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      Finset.sum_const_zero, add_zero, Function.comp_apply] using!
      (hc.tendsto (u, G)).comp hpair

/-- A genuine sequence of interior smooth approximants: every member is
supported inside U, and both physical value and Euclidean gradient converge. -/
theorem exists_physicalH1Graph_compact_interior_mollification_sequence
    (i : Fin d) (lam : ℝ) (u : Lp ℂ 2 (physicalForceMeasure i lam))
    (G : Fin d → Lp ℂ 2 (physicalForceMeasure i lam))
    (hu : IsPhysicalH1Graph (physicalForceMeasure i lam) (Or.inr ⟨i, lam, rfl⟩) u G)
    {K U : Set (Vec d)} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (huK : ∀ᵐ x ∂physicalForceMeasure i lam, x ∉ K → u x = 0) :
    ∃ (ε : ℕ → {ε : ℝ // 0 < ε})
      (v : ℕ → Lp ℂ 2 (physicalForceMeasure i lam))
      (H : ℕ → Fin d → Lp ℂ 2 (physicalForceMeasure i lam)),
      Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0) ∧
      (∀ n, IsPhysicalH1Graph (physicalForceMeasure i lam) (Or.inr ⟨i, lam, rfl⟩)
          (v n) (H n) ∧
        (v n : Vec d → ℂ) =ᵐ[physicalForceMeasure i lam] spatialSmoothMollify (ε n) u ∧
        (∀ j, (H n j : Vec d → ℂ) =ᵐ[physicalForceMeasure i lam]
          spatialSmoothMollify (ε n) (G j)) ∧
        ContDiff ℝ (⊤ : ℕ∞) (spatialSmoothMollify (ε n) u) ∧
        HasCompactSupport (spatialSmoothMollify (ε n) u) ∧
        tsupport (spatialSmoothMollify (ε n) u) ⊆ U) ∧
      Tendsto (fun n => ‖v n - u‖ ^ 2 + ∑ j : Fin d, ‖H n j - G j‖ ^ 2)
        atTop (𝓝 0) := by
  obtain ⟨v, H, hp, hsupp, hlim⟩ :=
    exists_physicalH1Graph_compact_interior_mollification i lam u G hu hK hU hKU huK
  let s (n : ℕ) : {ε : ℝ // 0 < ε} := ⟨1 / ((n : ℝ) + 1), by positivity⟩
  have hs : Tendsto s atTop (comap Subtype.val (𝓝 0)) :=
    tendsto_comap_iff.mpr tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hs.eventually hsupp)
  refine ⟨fun n => s (n + N), fun n => v (s (n + N)), fun n => H (s (n + N)),
    tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat N), ?_,
    hlim.comp (hs.comp (tendsto_add_atTop_nat N))⟩
  intro n
  obtain ⟨hg, hvr, hHr, hc, hk⟩ := hp (s (n + N))
  exact ⟨hg, hvr, hHr, hc, hk, hN (n + N) (Nat.le_add_left N n)⟩

end
end EinsteinFull
