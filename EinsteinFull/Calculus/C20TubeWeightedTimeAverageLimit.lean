import EinsteinFull.External.Source.GMPDirichletKernel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.SpecificCodomains.Pi

open EinsteinRelation MeasureTheory Filter
open scoped Topology ENNReal

namespace EinsteinFull.Calculus

/-- A continuous Banach-space path is recovered from its forward averages. -/
theorem c20_continuous_forward_average_tendsto
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : ℝ → E) (hf : Continuous f) :
    Tendsto (fun h : ℝ => h⁻¹ • ∫ s in (0 : ℝ)..h, f s)
      (𝓝[>] 0) (𝓝 (f 0)) := by
  have hd := (hf.integral_hasStrictDerivAt 0 0).hasDerivAt
  have hh := (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl (0 : ℝ))).mp
    (hd.hasDerivWithinAt (s := Set.Ioi 0))
  change Tendsto (fun h => slope (fun u : ℝ => ∫ s in (0 : ℝ)..u, f s) 0 h)
    (𝓝[>] 0) (𝓝 (f 0)) at hh
  simpa only [slope_def_module, sub_zero, intervalIntegral.integral_same] using hh

/-- Translation in the time coordinate as a continuous map. -/
def c20TimeTranslate {d : ℕ} (h : ℝ) : C(ℝ × Vec d, ℝ × Vec d) :=
  ⟨fun z => (z.1 + h, z.2), (continuous_fst.add continuous_const).prodMk continuous_snd⟩

theorem c20_time_translate_continuous {d : ℕ} :
    Continuous (fun h : ℝ => c20TimeTranslate (d := d) h) := by
  let g : C(ℝ × (ℝ × Vec d), ℝ × Vec d) :=
    ⟨fun p => (p.2.1 + p.1, p.2.2),
      ((continuous_fst.comp continuous_snd).add continuous_fst).prodMk
        (continuous_snd.comp continuous_snd)⟩
  exact g.curry.continuous

theorem c20_time_translate_measurePreserving {d : ℕ} (h : ℝ) :
    MeasurePreserving (c20TimeTranslate (d := d) h) volume volume := by
  have hm := (measurePreserving_add_left (volume : Measure ℝ) h).prod
      (MeasurePreserving.id (volume : Measure (Vec d)))
  convert hm using 1 <;> simp [c20TimeTranslate, add_comm]
  funext z
  cases z
  rfl

theorem c20_time_translate_L2_continuous {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] (f : Lp E 2 (volume : Measure (ℝ × Vec d))) :
    Continuous (fun h : ℝ => Lp.compMeasurePreserving (c20TimeTranslate h)
      (c20_time_translate_measurePreserving h) f) := by
  exact continuous_const.compMeasurePreservingLp c20_time_translate_continuous
    c20_time_translate_measurePreserving (by norm_num)

/-- Forward averages of the time translates converge in the global L² norm. -/
theorem c20_time_translate_forward_average_L2 {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : Lp E 2 (volume : Measure (ℝ × Vec d))) :
    Tendsto (fun h : ℝ => h⁻¹ • ∫ s in (0 : ℝ)..h,
      Lp.compMeasurePreserving (c20TimeTranslate s)
        (c20_time_translate_measurePreserving s) f) (𝓝[>] 0) (𝓝 f) := by
  have ht := c20_continuous_forward_average_tendsto
    (fun s => Lp.compMeasurePreserving (c20TimeTranslate s)
      (c20_time_translate_measurePreserving s) f) (c20_time_translate_L2_continuous f)
  have hz : ⇑(c20TimeTranslate (d := d) 0) = id := by
    funext z
    simp [c20TimeTranslate]
  simpa only [hz, Lp.compMeasurePreserving_id_apply] using ht

private theorem c20_integral_norm_le_l2 {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (f : Lp ℝ 2 μ) :
    ∫ x, ‖f x‖ ∂μ ≤ (μ Set.univ ^ (1 / 2 : ℝ)).toReal * ‖f‖ := by
  have hb : eLpNorm f 1 μ ≤ eLpNorm f 2 μ * μ Set.univ ^ (1 / 2 : ℝ) := by
    convert eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (Lp.aestronglyMeasurable f) using 1
    norm_num
  have hfin : eLpNorm f 2 μ * μ Set.univ ^ (1 / 2 : ℝ) ≠ ⊤ := by
    apply ENNReal.mul_ne_top (Lp.memLp f).ne
    finiteness
  have h := ENNReal.toReal_mono hfin hb
  rw [eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable f),
    ← integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable f),
    ENNReal.toReal_mul, ← Lp.norm_def] at h
  simpa only [mul_comm] using h

private theorem c20_integrable_joint_l2_finite {T Ω : Type*}
    [MeasurableSpace T] [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {ν : Measure T} {u : T → Lp ℝ 2 μ} (hu : Integrable u ν)
    {U : T × Ω → ℝ} (hU : Measurable U)
    (heq : ∀ t, (fun x => U (t, x)) =ᵐ[μ] u t) :
    Integrable U (ν.prod μ) := by
  apply (integrable_prod_iff hU.aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ (fun t => ((Lp.memLp (u t)).integrable (by norm_num)).congr
    (heq t).symm), ?_⟩
  apply (hu.norm.const_mul (μ Set.univ ^ (1 / 2 : ℝ)).toReal).mono'
    (hU.stronglyMeasurable.norm.integral_prod_right.aestronglyMeasurable)
  filter_upwards with t
  rw [Real.norm_of_nonneg (integral_nonneg (fun x => norm_nonneg _)),
    integral_congr_ae ((heq t).mono (fun x h => congrArg norm h))]
  exact c20_integral_norm_le_l2 (u t)

private theorem c20_coeFn_integral_joint_l2_finite {T Ω : Type*}
    [MeasurableSpace T] [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {ν : Measure T} [SFinite ν] {u : T → Lp ℝ 2 μ} (hu : Integrable u ν)
    {U : T × Ω → ℝ} (hU : Measurable U)
    (heq : ∀ t, (fun x => U (t, x)) =ᵐ[μ] u t) :
    (fun x => (∫ t, u t ∂ν) x) =ᵐ[μ] fun x => ∫ t, U (t, x) ∂ν := by
  have hi := c20_integrable_joint_l2_finite hu hU heq
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _
    ((Lp.memLp _).integrable (by norm_num)) hi.integral_prod_right
  intro A hA hμA
  have ht := integral_inner (𝕜 := ℝ) hu (indicatorConstLp 2 hA hμA.ne (1 : ℝ))
  rw [L2.inner_indicatorConstLp_one hA hμA.ne] at ht
  simp_rw [L2.inner_indicatorConstLp_one hA hμA.ne] at ht
  rw [← ht]
  have hir : Integrable U (ν.prod (μ.restrict A)) := by
    have h := hi.integrableOn (s := Set.univ ×ˢ A)
    rwa [IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ] at h
  rw [← integral_integral_swap (f := fun t x => U (t, x)) hir]
  apply integral_congr_ae
  filter_upwards with t
  exact integral_congr_ae (ae_restrict_of_ae (heq t).symm)

/-- On each finite spatial set, a measurable representative of an integrable
physical L2 curve has the literal pointwise time integral prescribed by its
Bochner integral. Spatial volume need not be finite. -/
private theorem c20_coeFn_integral_joint_l2_local {T Ω : Type*}
    [MeasurableSpace T] [MeasurableSpace Ω] {μ : Measure Ω}
    {ν : Measure T} [SFinite ν] {u : T → Lp ℝ 2 μ} (hu : Integrable u ν)
    {U : T × Ω → ℝ} (hU : Measurable U)
    (heq : ∀ t, (fun x => U (t, x)) =ᵐ[μ] u t)
    (K : Set Ω) (hK : μ K ≠ ⊤) :
    Integrable U (ν.prod (μ.restrict K)) ∧
      (fun x => (∫ t, u t ∂ν) x) =ᵐ[μ.restrict K] fun x => ∫ t, U (t, x) ∂ν := by
  let : IsFiniteMeasure (μ.restrict K) := ⟨by simpa using hK.lt_top⟩
  let C := LpToLpRestrictCLM Ω ℝ ℝ μ 2 K
  have hC : Integrable (fun t => C (u t)) ν := C.integrable_comp hu
  have hrep : ∀ t, (fun x => U (t, x)) =ᵐ[μ.restrict K] C (u t) := by
    intro t
    have ht : (fun x => U (t, x)) =ᵐ[μ.restrict K] (u t : Ω → ℝ) :=
      ae_restrict_of_ae (heq t)
    exact ht.trans (LpToLpRestrictCLM_coeFn ℝ K (u t)).symm
  refine ⟨c20_integrable_joint_l2_finite hC hU hrep, ?_⟩
  have hi := c20_coeFn_integral_joint_l2_finite hC hU hrep
  rw [C.integral_comp_comm hu] at hi
  exact (LpToLpRestrictCLM_coeFn ℝ K (∫ t, u t ∂ν)).symm.trans hi

/-- The L² Bochner integral agrees with the time integral of a joint
representative on a sigma-finite spatial measure. Finite restrictions justify
the identification before taking a countable spatial union. -/
theorem c20_coeFn_integral_joint_l2_sigmaFinite {T Ω : Type*}
    [MeasurableSpace T] [MeasurableSpace Ω] {μ : Measure Ω} [SigmaFinite μ]
    {ν : Measure T} [SFinite ν] {u : T → Lp ℝ 2 μ} (hu : Integrable u ν)
    {U : T × Ω → ℝ} (hU : Measurable U)
    (heq : ∀ t, (fun x => U (t, x)) =ᵐ[μ] u t) :
    (fun x => (∫ t, u t ∂ν) x) =ᵐ[μ] fun x => ∫ t, U (t, x) ∂ν := by
  have hi (n : ℕ) := (c20_coeFn_integral_joint_l2_local hu hU heq
    (spanningSets μ n) (measure_spanningSets_lt_top μ n).ne).2
  have h := (ae_restrict_iUnion_iff (spanningSets μ)
    (fun x => (∫ t, u t ∂ν) x = ∫ t, U (t, x) ∂ν)).mpr hi
  simpa only [iUnion_spanningSets, Measure.restrict_univ, Filter.EventuallyEq] using h


/-- The L² integral of translated data has the literal pointwise integral as representative. -/
theorem c20_time_translate_integral_ae {d : ℕ}
    (f : Lp ℝ 2 (volume : Measure (ℝ × Vec d)))
    (F : ℝ × Vec d → ℝ) (hF : Measurable F)
    (hrep : F =ᵐ[volume] f) {h : ℝ} (hh : 0 ≤ h) :
    (fun z => (∫ s in (0 : ℝ)..h,
      Lp.compMeasurePreserving (c20TimeTranslate s)
        (c20_time_translate_measurePreserving s) f) z) =ᵐ[volume]
      fun z => ∫ s in (0 : ℝ)..h, F (z.1 + s, z.2) := by
  let u : ℝ → Lp ℝ 2 (volume : Measure (ℝ × Vec d)) := fun s =>
    Lp.compMeasurePreserving (c20TimeTranslate s)
      (c20_time_translate_measurePreserving s) f
  let U : ℝ × (ℝ × Vec d) → ℝ := fun p => F (p.2.1 + p.1, p.2.2)
  have hu : Integrable u (volume.restrict (Set.Ioc 0 h)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hh).mp
      ((c20_time_translate_L2_continuous f).intervalIntegrable 0 h)
  have hU : Measurable U := hF.comp
    ((measurable_fst.comp measurable_snd).add measurable_fst |>.prodMk
      (measurable_snd.comp measurable_snd))
  have heq : ∀ s, (fun z => U (s, z)) =ᵐ[volume] u s := by
    intro s
    exact ((c20_time_translate_measurePreserving s).quasiMeasurePreserving.ae_eq_comp hrep).trans
      (Lp.coeFn_compMeasurePreserving f (c20_time_translate_measurePreserving s)).symm
  have hresult := c20_coeFn_integral_joint_l2_sigmaFinite hu hU heq
  simpa only [intervalIntegral.integral_of_le hh] using hresult

/-- Global L² convergence for the literal scalar forward average. -/
theorem c20_scalar_forward_average_global_L2 {d : ℕ}
    (f : Lp ℝ 2 (volume : Measure (ℝ × Vec d)))
    (F : ℝ × Vec d → ℝ) (hF : Measurable F)
    (hrep : F =ᵐ[volume] f) :
    Tendsto (fun h : ℝ => ∫ z, |h⁻¹ * (∫ s in (0 : ℝ)..h,
      F (z.1 + s, z.2)) - F z| ^ 2) (𝓝[>] 0) (𝓝 0) := by
  let q : ℝ → Lp ℝ 2 (volume : Measure (ℝ × Vec d)) := fun h =>
    h⁻¹ • ∫ s in (0 : ℝ)..h, Lp.compMeasurePreserving (c20TimeTranslate s)
      (c20_time_translate_measurePreserving s) f
  have hq : Tendsto q (𝓝[>] 0) (𝓝 f) := c20_time_translate_forward_average_L2 f
  have hn : Tendsto (fun h => ‖q h - f‖ ^ 2) (𝓝[>] 0) (𝓝 0) := by
    simpa using (hq.sub (tendsto_const_nhds : Tendsto (fun _ : ℝ => f) (𝓝[>] 0) (𝓝 f))).norm.pow 2
  apply hn.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have havg := c20_time_translate_integral_ae f F hF hrep (le_of_lt hh)
  have hsmul := Lp.coeFn_smul h⁻¹ (∫ s in (0 : ℝ)..h,
    Lp.compMeasurePreserving (c20TimeTranslate s)
      (c20_time_translate_measurePreserving s) f)
  have hsub := Lp.coeFn_sub (q h) f
  have he : (fun z => |h⁻¹ * (∫ s in (0 : ℝ)..h, F (z.1 + s, z.2)) - F z| ^ 2)
      =ᵐ[volume] (fun z => |(q h - f) z| ^ 2) := by
    filter_upwards [havg, hsmul, hsub, hrep] with z ha hs hd hr
    change (q h) z = h⁻¹ * (∫ s in (0 : ℝ)..h,
      Lp.compMeasurePreserving (c20TimeTranslate s)
        (c20_time_translate_measurePreserving s) f) z at hs
    rw [ha] at hs
    rw [← hs, hd, hr]
    rfl
  rw [integral_congr_ae he, ← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [Real.inner_apply, pow_two, abs_mul_abs_self]

/-- A global almost-everywhere change of data preserves its time integrals
for almost every base point, even when the original data are not measurable. -/
theorem c20_forward_integral_ae_congr {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : ℝ × Vec d → E) (hfg : f =ᵐ[volume] g) (h : ℝ) :
    ∀ᵐ z ∂(volume : Measure (ℝ × Vec d)),
      (∫ s in (0 : ℝ)..h, f (z.1 + s, z.2)) =
        ∫ s in (0 : ℝ)..h, g (z.1 + s, z.2) := by
  have hz : (volume : Measure (ℝ × Vec d)) {z | f z ≠ g z} = 0 :=
    ae_iff.mp hfg
  obtain ⟨N, hNsub, hNm, hNzero⟩ := exists_measurable_superset_of_null hz
  have hmeas : MeasurableSet {p : (ℝ × Vec d) × ℝ | (p.1.1 + p.2, p.1.2) ∉ N} :=
    (hNm.preimage (((measurable_fst.comp measurable_fst).add measurable_snd).prodMk
      (measurable_snd.comp measurable_fst))).compl
  have hs : ∀ᵐ s ∂(volume : Measure ℝ),
      ∀ᵐ z ∂(volume : Measure (ℝ × Vec d)), (z.1 + s, z.2) ∉ N := by
    filter_upwards with s
    have hn : ∀ᵐ z ∂(volume : Measure (ℝ × Vec d)), z ∉ N := ae_iff.mpr (by simpa using hNzero)
    exact (c20_time_translate_measurePreserving s).quasiMeasurePreserving.ae hn
  have hz' := (Measure.ae_ae_comm hmeas).mpr hs
  filter_upwards [hz'] with z hz
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hz] with s hs _
  by_contra hn
  exact hs (hNsub hn)

/-- The larger-slab zero extension agrees with the original forward integral
on the smaller slab for sufficiently short positive times. -/
theorem c20_forward_integral_indicator_slab {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Set (Vec d)) (f : ℝ × Vec d → E) (z : ℝ × Vec d) (h : ℝ)
    (hz : z ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ U)
    (hh : 0 ≤ h) (hh' : h ≤ 1 / 2) :
    (∫ s in (0 : ℝ)..h,
      ((Set.Ioo (-1 : ℝ) 1 ×ˢ U).indicator f) (z.1 + s, z.2)) =
      ∫ s in (0 : ℝ)..h, f (z.1 + s, z.2) := by
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le hh] at hs
  apply Set.indicator_of_mem
  exact ⟨⟨by linarith [hz.1.1, hs.1], by linarith [hz.1.2, hs.2]⟩, hz.2⟩

/-- A scalar average error of global L² data has integrable square. -/
theorem c20_scalar_forward_average_square_integrable {d : ℕ}
    (f : Lp ℝ 2 (volume : Measure (ℝ × Vec d)))
    (F : ℝ × Vec d → ℝ) (hF : Measurable F)
    (hrep : F =ᵐ[volume] f) {h : ℝ} (hh : 0 ≤ h) :
    Integrable (fun z => |h⁻¹ * (∫ s in (0 : ℝ)..h,
      F (z.1 + s, z.2)) - F z| ^ 2) := by
  let q : Lp ℝ 2 (volume : Measure (ℝ × Vec d)) :=
    h⁻¹ • ∫ s in (0 : ℝ)..h, Lp.compMeasurePreserving (c20TimeTranslate s)
      (c20_time_translate_measurePreserving s) f
  have havg := c20_time_translate_integral_ae f F hF hrep hh
  have hsmul := Lp.coeFn_smul h⁻¹ (∫ s in (0 : ℝ)..h,
    Lp.compMeasurePreserving (c20TimeTranslate s)
      (c20_time_translate_measurePreserving s) f)
  have hsub := Lp.coeFn_sub q f
  have he : (fun z => |(q - f) z| ^ 2) =ᵐ[volume]
      (fun z => |h⁻¹ * (∫ s in (0 : ℝ)..h, F (z.1 + s, z.2)) - F z| ^ 2) := by
    filter_upwards [havg, hsmul, hsub, hrep] with z ha hs hd hr
    change q z = h⁻¹ * (∫ s in (0 : ℝ)..h,
      Lp.compMeasurePreserving (c20TimeTranslate s)
        (c20_time_translate_measurePreserving s) f) z at hs
    rw [ha] at hs
    change (q - f) z = q z - f z at hd
    rw [hd, hs, hr]
  have hi := (Lp.memLp (q - f)).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  exact (by simpa only [Real.norm_eq_abs] using hi :
    Integrable (fun z => |(q - f) z| ^ 2)).congr he

/-- Scalar L² forward averages converge on a smaller time slab. -/
theorem c20_scalar_forward_average_slab_L2 {d : ℕ}
    (U : Set (Vec d)) (hU : MeasurableSet U) (u : ℝ × Vec d → ℝ)
    (hu : MemLp u 2 (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ U))) :
    Tendsto (fun h : ℝ => ∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ U,
      |h⁻¹ * (∫ s in (0 : ℝ)..h, u (z.1 + s, z.2)) - u z| ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
  let S := Set.Ioo (-1 : ℝ) 1 ×ˢ U
  let T := Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ U
  have hS : MeasurableSet S := measurableSet_Ioo.prod hU
  have hT : MeasurableSet T := measurableSet_Ioo.prod hU
  let v := S.indicator u
  have hv : MemLp v 2 (volume : Measure (ℝ × Vec d)) :=
    (memLp_indicator_iff_restrict hS).2 hu
  let F := hv.aestronglyMeasurable.mk v
  have hF : Measurable F := hv.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hvF : v =ᵐ[volume] F := hv.aestronglyMeasurable.ae_eq_mk
  let f := hv.toLp v
  have hFf : F =ᵐ[volume] f := hvF.symm.trans hv.coeFn_toLp.symm
  have hglobal := c20_scalar_forward_average_global_L2 f F hF hFf
  apply squeeze_zero' _ _ hglobal
  · exact Filter.Eventually.of_forall fun h => integral_nonneg fun z => sq_nonneg _
  · have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0, h < 1 / 2 :=
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hsmall] with h hh hhsmall
    have he : (fun z => |h⁻¹ * (∫ s in (0 : ℝ)..h, u (z.1 + s, z.2)) - u z| ^ 2)
        =ᵐ[volume.restrict T]
        (fun z => |h⁻¹ * (∫ s in (0 : ℝ)..h, F (z.1 + s, z.2)) - F z| ^ 2) := by
      filter_upwards [ae_restrict_of_ae (c20_forward_integral_ae_congr v F hvF h),
        ae_restrict_of_ae hvF, ae_restrict_mem hT] with z ha hb hz
      have hzS : z ∈ S := ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, hz.2⟩
      have hvz : v z = u z := Set.indicator_of_mem hzS _
      have havg := c20_forward_integral_indicator_slab U u z h hz (le_of_lt hh)
        (le_of_lt hhsmall)
      change (∫ s in (0 : ℝ)..h, v (z.1 + s, z.2)) = _ at havg
      rw [← havg, ha, ← hvz, hb]
    rw [integral_congr_ae he]
    exact integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall fun z => sq_nonneg _)
      (c20_scalar_forward_average_square_integrable f F hF hFf (le_of_lt hh))

/-- The scalar forward-average error has an integrable square on the smaller slab. -/
theorem c20_scalar_forward_average_slab_integrable {d : ℕ}
    (U : Set (Vec d)) (hU : MeasurableSet U) (u : ℝ × Vec d → ℝ)
    (hu : MemLp u 2 (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ U)))
    {h : ℝ} (hh : 0 ≤ h) (hhsmall : h ≤ 1 / 2) :
    Integrable (fun z => |h⁻¹ * (∫ s in (0 : ℝ)..h,
      u (z.1 + s, z.2)) - u z| ^ 2)
      (volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ U)) := by
  let S := Set.Ioo (-1 : ℝ) 1 ×ˢ U
  let T := Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ U
  have hS : MeasurableSet S := measurableSet_Ioo.prod hU
  have hT : MeasurableSet T := measurableSet_Ioo.prod hU
  let v := S.indicator u
  have hv : MemLp v 2 (volume : Measure (ℝ × Vec d)) :=
    (memLp_indicator_iff_restrict hS).2 hu
  let F := hv.aestronglyMeasurable.mk v
  have hF : Measurable F := hv.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hvF : v =ᵐ[volume] F := hv.aestronglyMeasurable.ae_eq_mk
  let f := hv.toLp v
  have hFf : F =ᵐ[volume] f := hvF.symm.trans hv.coeFn_toLp.symm
  have he : (fun z => |h⁻¹ * (∫ s in (0 : ℝ)..h, u (z.1 + s, z.2)) - u z| ^ 2)
      =ᵐ[volume.restrict T]
      (fun z => |h⁻¹ * (∫ s in (0 : ℝ)..h, F (z.1 + s, z.2)) - F z| ^ 2) := by
    filter_upwards [ae_restrict_of_ae (c20_forward_integral_ae_congr v F hvF h),
      ae_restrict_of_ae hvF, ae_restrict_mem hT] with z ha hb hz
    have hzS : z ∈ S := ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, hz.2⟩
    have hvz : v z = u z := Set.indicator_of_mem hzS _
    have havg := c20_forward_integral_indicator_slab U u z h hz hh hhsmall
    change (∫ s in (0 : ℝ)..h, v (z.1 + s, z.2)) = _ at havg
    rw [← havg, ha, ← hvz, hb]
  exact (c20_scalar_forward_average_square_integrable f F hF hFf hh).integrableOn.congr he.symm

/-- A bounded nonnegative weight preserves scalar slab convergence. -/
theorem c20_scalar_weighted_forward_average_slab_L2 {d : ℕ}
    (U : Set (Vec d)) (hU : MeasurableSet U) (u : ℝ × Vec d → ℝ)
    (hu : MemLp u 2 (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ U)))
    (ρ : Vec d → ℝ) (C : ℝ) (hρ : ∀ x, 0 ≤ ρ x ∧ ρ x ≤ C) :
    Tendsto (fun h : ℝ => ∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ U,
      ρ z.2 * |h⁻¹ * (∫ s in (0 : ℝ)..h, u (z.1 + s, z.2)) - u z| ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
  have hlim := (c20_scalar_forward_average_slab_L2 U hU u hu).const_mul C
  simp only [mul_zero] at hlim
  apply squeeze_zero' _ _ hlim
  · exact Filter.Eventually.of_forall fun h => integral_nonneg fun z =>
      mul_nonneg (hρ z.2).1 (sq_nonneg _)
  · have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0, h < 1 / 2 :=
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hsmall] with h hh hhsmall
    rw [← integral_const_mul]
    apply integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall fun z => mul_nonneg (hρ z.2).1 (sq_nonneg _)
    · exact (c20_scalar_forward_average_slab_integrable U hU u hu
        (le_of_lt hh) (le_of_lt hhsmall)).const_mul C
    · exact Filter.Eventually.of_forall fun z =>
        mul_le_mul_of_nonneg_right (hρ z.2).2 (sq_nonneg _)

/-- Euclidean finite energy implies finite energy in the coordinate-space norm. -/
theorem c20_vector_memLp_of_euclidean {d : ℕ} {μ : Measure (ℝ × Vec d)}
    (G : ℝ × Vec d → Vec d) (hGm : AEStronglyMeasurable G μ)
    (hG : MemLp (fun z => euclideanNorm (G z)) 2 μ) : MemLp G 2 μ := by
  apply hG.mono' hGm
  filter_upwards with z
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2
  intro i
  rw [Real.norm_eq_abs]
  unfold euclideanSq dot
  apply Real.abs_le_sqrt
  rw [sq]
  exact Finset.single_le_sum (f := fun j => G z j * G z j)
    (fun j _ => mul_self_nonneg _) (Finset.mem_univ i)

/-- Euclidean source balls are measurable in the coordinate carrier. -/
theorem c20_sourceBall_measurable {d : ℕ} (y : Vec d) (r : ℝ) :
    MeasurableSet (EinsteinFull.External.Source.GMP.sourceBall y r) := by
  have hc : Continuous (fun x : Vec d => euclideanNorm x) := by
    unfold euclideanNorm euclideanSq dot
    exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ =>
      (continuous_apply i).mul (continuous_apply i))
  exact (isOpen_lt (hc.comp (continuous_id.sub continuous_const))
    continuous_const).measurableSet

/-- The scalar part of the weighted convergence follows from ellipticity. -/
theorem c20_elliptic_scalar_forward_average_L2 {d : ℕ} {κ r : ℝ}
    (hκ : 0 < κ) (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : EinsteinFull.External.Source.GMP.IsUniformlyElliptic κ ρ α)
    (y : Vec d) (u : ℝ × Vec d → ℝ)
    (hu : MemLp u 2 (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ
      EinsteinFull.External.Source.GMP.sourceBall y r))) :
    Tendsto (fun h : ℝ => ∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
      EinsteinFull.External.Source.GMP.sourceBall y r,
      ρ z.2 * |h⁻¹ * (∫ s in (0 : ℝ)..h, u (z.1 + s, z.2)) - u z| ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
  apply c20_scalar_weighted_forward_average_slab_L2 _ (c20_sourceBall_measurable y r)
    u hu ρ κ⁻¹
  intro x
  exact ⟨le_trans (le_of_lt hκ) (hell.2.2 x).1, (hell.2.2 x).2.1⟩

/-- On a sigma-finite space, time sections of an integrable L² curve are
integrable almost everywhere, for a jointly measurable representative. -/
theorem c20_joint_l2_time_integrable_ae {T Ω : Type*}
    [MeasurableSpace T] [MeasurableSpace Ω] {μ : Measure Ω} [SigmaFinite μ]
    {ν : Measure T} [SFinite ν] {u : T → Lp ℝ 2 μ} (hu : Integrable u ν)
    {U : T × Ω → ℝ} (hU : Measurable U)
    (heq : ∀ t, (fun x => U (t, x)) =ᵐ[μ] u t) :
    ∀ᵐ x ∂μ, Integrable (fun t => U (t, x)) ν := by
  have hi (n : ℕ) : ∀ᵐ x ∂μ.restrict (spanningSets μ n),
      Integrable (fun t => U (t, x)) ν :=
    (c20_coeFn_integral_joint_l2_local hu hU heq (spanningSets μ n)
      (measure_spanningSets_lt_top μ n).ne).1.prod_left_ae
  have h := (ae_restrict_iUnion_iff (spanningSets μ)
    (fun x => Integrable (fun t => U (t, x)) ν)).mpr hi
  simpa only [iUnion_spanningSets, Measure.restrict_univ] using h

/-- Almost-everywhere equal data have almost-everywhere equal time sections. -/
theorem c20_forward_sections_ae_congr {d : ℕ} {E : Type*}
    (f g : ℝ × Vec d → E) (hfg : f =ᵐ[volume] g) (h : ℝ) :
    ∀ᵐ z ∂(volume : Measure (ℝ × Vec d)),
      (fun s => f (z.1 + s, z.2)) =ᵐ[volume.restrict (Set.Ioc 0 h)]
        (fun s => g (z.1 + s, z.2)) := by
  have hz : (volume : Measure (ℝ × Vec d)) {z | f z ≠ g z} = 0 := ae_iff.mp hfg
  obtain ⟨N, hNsub, hNm, hNzero⟩ := exists_measurable_superset_of_null hz
  have hm : MeasurableSet {p : (ℝ × Vec d) × ℝ | (p.1.1 + p.2, p.1.2) ∉ N} :=
    (hNm.preimage (((measurable_fst.comp measurable_fst).add measurable_snd).prodMk
      (measurable_snd.comp measurable_fst))).compl
  have hs : ∀ᵐ s ∂(volume : Measure ℝ),
      ∀ᵐ z ∂(volume : Measure (ℝ × Vec d)), (z.1 + s, z.2) ∉ N := by
    filter_upwards with s
    have hn : ∀ᵐ z ∂(volume : Measure (ℝ × Vec d)), z ∉ N :=
      ae_iff.mpr (by simpa using hNzero)
    exact (c20_time_translate_measurePreserving s).quasiMeasurePreserving.ae hn
  have hz' := (Measure.ae_ae_comm hm).mpr hs
  filter_upwards [hz'] with z hz
  filter_upwards [ae_restrict_of_ae hz] with s hs
  by_contra hn
  exact hs (hNsub hn)

/-- Scalar finite-energy data have integrable short forward sections almost everywhere. -/
theorem c20_scalar_forward_section_integrable_ae {d : ℕ}
    (U : Set (Vec d)) (hU : MeasurableSet U) (u : ℝ × Vec d → ℝ)
    (hu : MemLp u 2 (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ U)))
    {h : ℝ} (hh : 0 ≤ h) (hhsmall : h ≤ 1 / 2) :
    ∀ᵐ z ∂volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ U),
      Integrable (fun s => u (z.1 + s, z.2)) (volume.restrict (Set.Ioc 0 h)) := by
  let S := Set.Ioo (-1 : ℝ) 1 ×ˢ U
  let T := Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ U
  have hS : MeasurableSet S := measurableSet_Ioo.prod hU
  have hT : MeasurableSet T := measurableSet_Ioo.prod hU
  let v := S.indicator u
  have hv : MemLp v 2 (volume : Measure (ℝ × Vec d)) :=
    (memLp_indicator_iff_restrict hS).2 hu
  let F := hv.aestronglyMeasurable.mk v
  have hF : Measurable F := hv.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hvF : v =ᵐ[volume] F := hv.aestronglyMeasurable.ae_eq_mk
  let f := hv.toLp v
  have hFf : F =ᵐ[volume] f := hvF.symm.trans hv.coeFn_toLp.symm
  let path : ℝ → Lp ℝ 2 (volume : Measure (ℝ × Vec d)) := fun s =>
    Lp.compMeasurePreserving (c20TimeTranslate s) (c20_time_translate_measurePreserving s) f
  let V : ℝ × (ℝ × Vec d) → ℝ := fun p => F (p.2.1 + p.1, p.2.2)
  have hp : Integrable path (volume.restrict (Set.Ioc 0 h)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hh).mp
      ((c20_time_translate_L2_continuous f).intervalIntegrable 0 h)
  have hV : Measurable V := hF.comp
    ((measurable_fst.comp measurable_snd).add measurable_fst |>.prodMk
      (measurable_snd.comp measurable_snd))
  have heq : ∀ s, (fun z => V (s, z)) =ᵐ[volume] path s := by
    intro s
    exact ((c20_time_translate_measurePreserving s).quasiMeasurePreserving.ae_eq_comp hFf).trans
      (Lp.coeFn_compMeasurePreserving f (c20_time_translate_measurePreserving s)).symm
  have hi := c20_joint_l2_time_integrable_ae hp hV heq
  filter_upwards [ae_restrict_of_ae hi, ae_restrict_of_ae
    (c20_forward_sections_ae_congr v F hvF h), ae_restrict_mem hT] with z hz he hzT
  apply hz.congr
  filter_upwards [he.symm, ae_restrict_mem measurableSet_Ioc] with s hs hsI
  have hsS : (z.1 + s, z.2) ∈ S :=
    ⟨⟨by linarith [hzT.1.1, hsI.1], by linarith [hzT.1.2, hsI.2]⟩, hzT.2⟩
  change F (z.1 + s, z.2) = u (z.1 + s, z.2)
  rw [hs]
  exact Set.indicator_of_mem hsS _

/-- On almost every short forward section, vector integration commutes with
coordinate evaluation. -/
theorem c20_vector_forward_integral_eval_ae {d : ℕ}
    (U : Set (Vec d)) (hU : MeasurableSet U) (G : ℝ × Vec d → Vec d)
    (hG : MemLp G 2 (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ U)))
    {h : ℝ} (hh : 0 ≤ h) (hhsmall : h ≤ 1 / 2) :
    ∀ᵐ z ∂volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ U),
      ∀ i : Fin d, (∫ s in (0 : ℝ)..h, G (z.1 + s, z.2)) i =
        ∫ s in (0 : ℝ)..h, G (z.1 + s, z.2) i := by
  have hc (i : Fin d) : MemLp (fun z => G z i) 2
      (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ U)) := hG.eval i
  have hi (i : Fin d) := c20_scalar_forward_section_integrable_ae U hU
    (fun z => G z i) (hc i) hh hhsmall
  filter_upwards [Filter.eventually_all.mpr hi] with z hz i
  simp only [intervalIntegral.integral_of_le hh]
  exact MeasureTheory.eval_integral hz i

/-- Forward averages converge in Euclidean L² on a smaller slab. -/
theorem c20_vector_forward_average_slab_L2 {d : ℕ}
    (U : Set (Vec d)) (hU : MeasurableSet U) (G : ℝ × Vec d → Vec d)
    (hG : MemLp G 2 (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ U))) :
    Tendsto (fun h : ℝ => ∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ U,
      euclideanNorm (h⁻¹ • (∫ s in (0 : ℝ)..h, G (z.1 + s, z.2)) - G z) ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
  have hc (i : Fin d) : MemLp (fun z => G z i) 2
      (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ U)) := hG.eval i
  have hlim := tendsto_finset_sum Finset.univ (fun i _ =>
    c20_scalar_forward_average_slab_L2 U hU (fun z => G z i) (hc i))
  simp only [Finset.sum_const_zero] at hlim
  apply hlim.congr'
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0, h < 1 / 2 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with h hh hhsmall
  have hi (i : Fin d) := c20_scalar_forward_average_slab_integrable U hU
    (fun z => G z i) (hc i) (le_of_lt hh) (le_of_lt hhsmall)
  rw [← integral_finset_sum Finset.univ (fun i _ => hi i)]
  apply integral_congr_ae
  filter_upwards [c20_vector_forward_integral_eval_ae U hU G hG
    (le_of_lt hh) (le_of_lt hhsmall)] with z hz
  unfold euclideanNorm euclideanSq dot
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => mul_self_nonneg _)]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hz i, pow_two, abs_mul_abs_self]

/-- Weighted scalar and Euclidean gradient forward averages converge in L². -/
theorem c20_weighted_forward_average_L2_limit
    {d : ℕ} {κ r : ℝ} (hκ : 0 < κ)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : EinsteinFull.External.Source.GMP.IsUniformlyElliptic κ ρ α)
    (y : Vec d) (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : MemLp u 2 (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ
      EinsteinFull.External.Source.GMP.sourceBall y r)))
    (hGm : AEStronglyMeasurable G (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ
      EinsteinFull.External.Source.GMP.sourceBall y r)))
    (hG : MemLp (fun z => euclideanNorm (G z)) 2
      (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ EinsteinFull.External.Source.GMP.sourceBall y r))) :
    let I := Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)
    let U := EinsteinFull.External.Source.GMP.sourceBall y r
    let uh := fun (h : ℝ) (z : ℝ × Vec d) =>
      h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1 + s, z.2)
    let Gh := fun (h : ℝ) (z : ℝ × Vec d) =>
      h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1 + s, z.2)
    Tendsto (fun h : ℝ => ∫ z in I ×ˢ U, ρ z.2 * |uh h z - u z| ^ 2)
      (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun h : ℝ => ∫ z in I ×ˢ U, euclideanNorm (Gh h z - G z) ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
  exact ⟨c20_elliptic_scalar_forward_average_L2 hκ ρ α hell y u hu,
    c20_vector_forward_average_slab_L2 _ (c20_sourceBall_measurable y r) G
      (c20_vector_memLp_of_euclidean G hGm hG)⟩


/-- Forward averages converge for the actual weighted-caloric solution and its gradient. -/
theorem c20_weighted_caloric_forward_average_L2_limit
    {d : ℕ} {κ r : ℝ} (hκ : 0 < κ)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : EinsteinFull.External.Source.GMP.IsUniformlyElliptic κ ρ α)
    (y : Vec d) (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : EinsteinFull.External.Source.GMP.IsWeightedCaloric ρ α
      (Set.Ioo (-1 : ℝ) 1) (EinsteinFull.External.Source.GMP.sourceBall y r) u G) :
    let I := Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)
    let U := EinsteinFull.External.Source.GMP.sourceBall y r
    let uh := fun (h : ℝ) (z : ℝ × Vec d) =>
      h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1 + s, z.2)
    let Gh := fun (h : ℝ) (z : ℝ × Vec d) =>
      h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1 + s, z.2)
    Tendsto (fun h : ℝ => ∫ z in I ×ˢ U, ρ z.2 * |uh h z - u z| ^ 2)
      (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun h : ℝ => ∫ z in I ×ˢ U, euclideanNorm (Gh h z - G z) ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
  exact c20_weighted_forward_average_L2_limit hκ ρ α hell y u G
    hcal.1 hcal.2.1 hcal.2.2.1

end EinsteinFull.Calculus
