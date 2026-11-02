import EinsteinFull.External.Source.GMPDirichletKernel
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Normed.Module.Convex
import EinsteinRelation.Regeneration.HalfSpaces
import EinsteinRelation.Environment.EuclideanLipschitz

open MeasureTheory

namespace EinsteinFull.Calculus

/-- The forward average stays inside the original time interval. -/
theorem c18_forward_time_mem {h t s : ℝ} (hh : h ≤ 1 / 4)
    (ht : t ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2))
    (hs : s ∈ Set.Icc 0 h) : t + s ∈ Set.Ioo (-1 : ℝ) 1 := by
  rcases ht with ⟨htl, htu⟩
  rcases hs with ⟨hsl, hsu⟩
  constructor <;> linarith

/-- An almost-everywhere property on the original interval holds for almost
every forward shift at almost every time in the smaller interval. -/
theorem c18_ae_forward_time {h : ℝ} (hh : h ≤ 1 / 4) {P : ℝ → Prop}
    (hP : ∀ᵐ t ∂volume.restrict (Set.Ioo (-1 : ℝ) 1), P t) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)),
      ∀ᵐ s ∂volume.restrict (Set.Ioc (0 : ℝ) h), P (t + s) := by
  have hP' : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Ioo (-1 : ℝ) 1 → P t :=
    (ae_restrict_iff' measurableSet_Ioo).mp hP
  have hs : ∀ᵐ z ∂((volume : Measure ℝ).prod volume),
      z.1 + z.2 ∈ Set.Ioo (-1 : ℝ) 1 → P (z.1 + z.2) := by
    have hp := (measurePreserving_add_prod (volume : Measure ℝ) volume).quasiMeasurePreserving.ae
      ((Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℝ))
        (ν := (volume : Measure ℝ))).ae hP')
    exact hp
  have hs' := Measure.ae_ae_of_ae_prod hs
  filter_upwards [ae_restrict_of_ae hs', ae_restrict_mem measurableSet_Ioo] with t ht htmem
  filter_upwards [ae_restrict_of_ae ht, ae_restrict_mem measurableSet_Ioc] with s hs hsmem
  exact hs (c18_forward_time_mem hh htmem ⟨le_of_lt hsmem.1, hsmem.2⟩)

/-- The actual weak gradients are available at almost every shifted slice. -/
theorem c18_weighted_caloric_ae_shifted_gradient {d : ℕ} {h r : ℝ}
    (hh : h ≤ 1 / 4) (ρ : EinsteinRelation.Vec d → ℝ)
    (α : EinsteinRelation.Vec d → EinsteinRelation.Mat d) (y : EinsteinRelation.Vec d)
    (u : ℝ × EinsteinRelation.Vec d → ℝ) (G : ℝ × EinsteinRelation.Vec d → EinsteinRelation.Vec d)
    (hu : EinsteinFull.External.Source.GMP.IsWeightedCaloric ρ α (Set.Ioo (-1) 1)
      (EinsteinFull.External.Source.GMP.sourceBall y r) u G) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)),
      ∀ᵐ s ∂volume.restrict (Set.Ioc (0 : ℝ) h),
        EinsteinRelation.HasWeakGradient (EinsteinFull.External.Source.GMP.sourceBall y r)
          (fun x => u (t + s, x)) (fun x => G (t + s, x)) :=
  c18_ae_forward_time hh hu.2.2.2.1

/-- A fixed forward translation preserves square integrability on the smaller
cylinder. The spatial domain remains unchanged. -/
theorem c18_memLp_forward_shift {E : Type*} [NormedAddCommGroup E]
    {d : ℕ} {h s : ℝ} {U : Set (EinsteinRelation.Vec d)}
    (hU : MeasurableSet U) (hh : h ≤ 1 / 4) (hs : s ∈ Set.Icc 0 h)
    {u : ℝ × EinsteinRelation.Vec d → E}
    (hu : MemLp u 2 (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ U))) :
    MemLp (fun z => u (z.1 + s, z.2)) 2
      (volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ U)) ∧
    eLpNorm (fun z => u (z.1 + s, z.2)) 2
      (volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ U)) ≤
      eLpNorm u 2 (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ U)) := by
  let A := Set.Ioo (-1 : ℝ) 1 ×ˢ U
  let B := Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ U
  have hA : MeasurableSet A := measurableSet_Ioo.prod hU
  have hB : MeasurableSet B := measurableSet_Ioo.prod hU
  have hzero : MemLp (A.indicator u) 2 (volume : Measure (ℝ × EinsteinRelation.Vec d)) :=
    (memLp_indicator_iff_restrict hA).2 hu
  have hshift := hzero.comp_measurePreserving
    ((measurePreserving_add_right (volume : Measure ℝ) s).prod
      (MeasurePreserving.id (volume : Measure (EinsteinRelation.Vec d))))
  have hrestrict := hshift.mono_measure (Measure.restrict_le_self :
    (volume.restrict B : Measure (ℝ × EinsteinRelation.Vec d)) ≤ volume)
  have heq : (A.indicator u ∘ Prod.map (fun t : ℝ => t + s) id) =ᵐ[volume.restrict B]
      (fun z => u (z.1 + s, z.2)) := by
    filter_upwards [ae_restrict_mem hB] with z hz
    change A.indicator u (z.1 + s, z.2) = u (z.1 + s, z.2)
    apply Set.indicator_of_mem
    exact ⟨c18_forward_time_mem hh hz.1 hs, hz.2⟩
  refine ⟨MemLp.ae_eq heq hrestrict, ?_⟩
  calc
    _ = eLpNorm (A.indicator u ∘ Prod.map (fun t : ℝ => t + s) id) 2
        (volume.restrict B) := (eLpNorm_congr_ae heq).symm
    _ ≤ eLpNorm (A.indicator u ∘ Prod.map (fun t : ℝ => t + s) id) 2 volume :=
      eLpNorm_mono_measure _ Measure.restrict_le_self
    _ = eLpNorm (A.indicator u) 2 volume :=
      eLpNorm_comp_measurePreserving hzero.aestronglyMeasurable
        ((measurePreserving_add_right (volume : Measure ℝ) s).prod
          (MeasurePreserving.id (volume : Measure (EinsteinRelation.Vec d))))
    _ = _ := eLpNorm_indicator_eq_eLpNorm_restrict hA

/-- Integrable cylinder data have integrable forward time slices at almost every
spatial point. -/
theorem c18_ae_intervalIntegrable_forward {E : Type*} [NormedAddCommGroup E]
    {d : ℕ} {h : ℝ} {U : Set (EinsteinRelation.Vec d)}
    (hh : 0 ≤ h) (hhsmall : h ≤ 1 / 4)
    {u : ℝ × EinsteinRelation.Vec d → E}
    (hu : Integrable u (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ U))) :
    ∀ᵐ x ∂volume.restrict U, ∀ t ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2),
      IntervalIntegrable (fun s => u (t + s, x)) volume 0 h := by
  have hprod : Integrable u ((volume.restrict (Set.Ioo (-1 : ℝ) 1)).prod
      (volume.restrict U)) := by
    rw [Measure.prod_restrict]
    exact hu
  filter_upwards [hprod.prod_left_ae] with x hx t ht
  change IntegrableOn (fun q => u (q, x)) (Set.Ioo (-1 : ℝ) 1) at hx
  have hinterval : IntervalIntegrable (fun q => u (q, x)) volume t (t + h) := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).2
    apply hx.mono_set
    intro q hq
    have hs : q - t ∈ Set.Icc (0 : ℝ) h := by constructor <;> linarith [hq.1, hq.2]
    have hm := c18_forward_time_mem hhsmall ht hs
    simpa using hm
  simpa using hinterval.comp_add_left t

/-- Square-integrable cylinder data admit forward time integrals whenever the
cylinder has finite measure. -/
theorem c18_ae_intervalIntegrable_forward_of_memLp {E : Type*} [NormedAddCommGroup E]
    {d : ℕ} {h : ℝ} {U : Set (EinsteinRelation.Vec d)}
    (hh : 0 ≤ h) (hhsmall : h ≤ 1 / 4)
    [IsFiniteMeasure (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ U))]
    {u : ℝ × EinsteinRelation.Vec d → E}
    (hu : MemLp u 2 (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ U))) :
    ∀ᵐ x ∂volume.restrict U, ∀ t ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2),
      IntervalIntegrable (fun s => u (t + s, x)) volume 0 h :=
  c18_ae_intervalIntegrable_forward hh hhsmall
    (memLp_one_iff_integrable.mp (hu.mono_exponent (by norm_num)))

/-- Forward translates are jointly almost-everywhere strongly measurable in
shift and space-time, including for merely almost-everywhere measurable data. -/
theorem c18_aeStronglyMeasurable_forward_joint {E : Type*} [NormedAddCommGroup E]
    {d : ℕ} {h : ℝ} {U : Set (EinsteinRelation.Vec d)}
    (hU : MeasurableSet U) (hhsmall : h ≤ 1 / 4)
    {u : ℝ × EinsteinRelation.Vec d → E}
    (hu : AEStronglyMeasurable u (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ U))) :
    AEStronglyMeasurable (fun p : ℝ × (ℝ × EinsteinRelation.Vec d) =>
      u (p.2.1 + p.1, p.2.2))
      ((volume.restrict (Set.Ioc (0 : ℝ) h)).prod
        (volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ U))) := by
  let A := Set.Ioo (-1 : ℝ) 1 ×ˢ U
  let B := Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ U
  let μ := (volume : Measure ℝ).restrict (Set.Ioc 0 h)
  let ν := (volume : Measure (ℝ × EinsteinRelation.Vec d))
  have hA : MeasurableSet A := measurableSet_Ioo.prod hU
  have hB : MeasurableSet B := measurableSet_Ioo.prod hU
  have hzero : AEStronglyMeasurable (A.indicator u) ν :=
    (aestronglyMeasurable_indicator_iff hA).2 hu
  have hskew : MeasurePreserving
      (fun p : ℝ × (ℝ × EinsteinRelation.Vec d) => (p.1, (p.2.1 + p.1, p.2.2)))
      (μ.prod ν) (μ.prod ν) := by
    refine MeasurePreserving.skew_product (g := fun (s : ℝ) (z : ℝ × EinsteinRelation.Vec d) => (z.1 + s, z.2))
      (MeasurePreserving.id μ) ?_ ?_
    · exact ((measurable_fst.comp measurable_snd).add measurable_fst).prodMk
        (measurable_snd.comp measurable_snd)
    · exact Filter.Eventually.of_forall fun s =>
        ((measurePreserving_add_right (volume : Measure ℝ) s).prod
          (MeasurePreserving.id (volume : Measure (EinsteinRelation.Vec d)))).map_eq
  have hshift := hzero.comp_snd.comp_quasiMeasurePreserving hskew.quasiMeasurePreserving
  have hrestrict : AEStronglyMeasurable
      (fun p : ℝ × (ℝ × EinsteinRelation.Vec d) => A.indicator u (p.2.1 + p.1, p.2.2))
      (μ.prod (ν.restrict B)) :=
    hshift.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  apply hrestrict.congr
  have hs := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν.restrict B)).ae
    (ae_restrict_mem measurableSet_Ioc)
  have hz := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν.restrict B)).ae
    (ae_restrict_mem hB)
  filter_upwards [hs, hz] with p hp hpB
  change A.indicator u (p.2.1 + p.1, p.2.2) = u (p.2.1 + p.1, p.2.2)
  apply Set.indicator_of_mem
  exact ⟨c18_forward_time_mem hhsmall hpB.1 ⟨le_of_lt hp.1, hp.2⟩, hpB.2⟩

/-- Forward shifts are jointly square integrable in the shift and the smaller
space-time cylinder. -/
theorem c18_memLp_forward_joint {E : Type*} [NormedAddCommGroup E]
    {d : ℕ} {h : ℝ} {U : Set (EinsteinRelation.Vec d)}
    (hU : MeasurableSet U) (hhsmall : h ≤ 1 / 4)
    {u : ℝ × EinsteinRelation.Vec d → E}
    (hu : MemLp u 2 (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ U))) :
    MemLp (fun p : ℝ × (ℝ × EinsteinRelation.Vec d) => u (p.2.1 + p.1, p.2.2)) 2
      ((volume.restrict (Set.Ioc (0 : ℝ) h)).prod
        (volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ U))) := by
  let A := Set.Ioo (-1 : ℝ) 1 ×ˢ U
  let B := Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ U
  let μ := (volume : Measure ℝ).restrict (Set.Ioc 0 h)
  let ν := (volume : Measure (ℝ × EinsteinRelation.Vec d))
  have hA : MeasurableSet A := measurableSet_Ioo.prod hU
  have hB : MeasurableSet B := measurableSet_Ioo.prod hU
  have hzero : MemLp (A.indicator u) 2 ν := (memLp_indicator_iff_restrict hA).2 hu
  have hskew : MeasurePreserving
      (fun p : ℝ × (ℝ × EinsteinRelation.Vec d) => (p.1, (p.2.1 + p.1, p.2.2)))
      (μ.prod ν) (μ.prod ν) := by
    refine MeasurePreserving.skew_product
      (g := fun (s : ℝ) (z : ℝ × EinsteinRelation.Vec d) => (z.1 + s, z.2))
      (MeasurePreserving.id μ) ?_ ?_
    · exact ((measurable_fst.comp measurable_snd).add measurable_fst).prodMk
        (measurable_snd.comp measurable_snd)
    · exact Filter.Eventually.of_forall fun s =>
        ((measurePreserving_add_right (volume : Measure ℝ) s).prod
          (MeasurePreserving.id (volume : Measure (EinsteinRelation.Vec d)))).map_eq
  have hshift := (hzero.comp_snd μ).comp_measurePreserving hskew
  have hrestrict : MemLp
      (fun p : ℝ × (ℝ × EinsteinRelation.Vec d) => A.indicator u (p.2.1 + p.1, p.2.2)) 2
      (μ.prod (ν.restrict B)) :=
    hshift.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  apply MemLp.ae_eq ?_ hrestrict
  have hs := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν.restrict B)).ae
    (ae_restrict_mem measurableSet_Ioc)
  have hz := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν.restrict B)).ae
    (ae_restrict_mem hB)
  filter_upwards [hs, hz] with p hp hpB
  change A.indicator u (p.2.1 + p.1, p.2.2) = u (p.2.1 + p.1, p.2.2)
  apply Set.indicator_of_mem
  exact ⟨c18_forward_time_mem hhsmall hpB.1 ⟨le_of_lt hp.1, hp.2⟩, hpB.2⟩

/-- Squared norms of forward shifts are integrable on almost every time
slice, and their forward integrals are integrable on the smaller cylinder. -/
theorem c18_forward_shift_norm_sq_integrable {E : Type*} [NormedAddCommGroup E]
    {d : ℕ} {h : ℝ} {U : Set (EinsteinRelation.Vec d)}
    (hU : MeasurableSet U) (hh : 0 ≤ h) (hhsmall : h ≤ 1 / 4)
    {u : ℝ × EinsteinRelation.Vec d → E}
    (hu : MemLp u 2 (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ U))) :
    (∀ᵐ z ∂volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ U),
      Integrable (fun s : ℝ => ‖u (z.1 + s, z.2)‖ ^ 2)
        (volume.restrict (Set.Ioc 0 h))) ∧
    Integrable (fun z => ∫ s in (0 : ℝ)..h, ‖u (z.1 + s, z.2)‖ ^ 2)
      (volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ U)) := by
  have hj := (c18_memLp_forward_joint hU hhsmall hu).integrable_norm_pow (by norm_num)
  refine ⟨hj.prod_left_ae, ?_⟩
  simpa only [intervalIntegral.integral_of_le hh, Real.norm_eq_abs, abs_pow, abs_norm]
    using hj.integral_norm_prod_right

/-- Jensen's inequality for the squared norm of a forward time average. -/
theorem c18_forward_average_norm_sq_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {h : ℝ} (hh : 0 < h)
    (f : ℝ → E) (hf : IntegrableOn f (Set.Ioc 0 h))
    (hf2 : IntegrableOn (fun s => ‖f s‖ ^ 2) (Set.Ioc 0 h)) :
    ‖h⁻¹ • ∫ s in (0 : ℝ)..h, f s‖ ^ 2 ≤
      h⁻¹ * ∫ s in (0 : ℝ)..h, ‖f s‖ ^ 2 := by
  have hc : ConvexOn ℝ (Set.univ : Set E) (fun x => ‖x‖ ^ 2) := by
    convert (convexOn_univ_norm (E := E)).pow (fun _ _ => norm_nonneg _) 2 using 1
  have h0 : (volume : Measure ℝ) (Set.Ioc 0 h) ≠ 0 := by
    simp [Real.volume_Ioc, hh]
  have ht : (volume : Measure ℝ) (Set.Ioc 0 h) ≠ ⊤ := by simp
  have hj := hc.map_set_average_le (by fun_prop) isClosed_univ h0 ht
    (Filter.Eventually.of_forall fun _ => Set.mem_univ _) hf hf2
  simpa [MeasureTheory.setAverage_eq, Real.volume_real_Ioc_of_le hh.le,
    intervalIntegral.integral_of_le hh.le] using hj

/-- Forward time integration preserves almost-everywhere strong measurability. -/
theorem c18_aeStronglyMeasurable_forward_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {d : ℕ} {h : ℝ} {U : Set (EinsteinRelation.Vec d)}
    (hU : MeasurableSet U) (hh : 0 ≤ h) (hhsmall : h ≤ 1 / 4)
    {u : ℝ × EinsteinRelation.Vec d → E}
    (hu : AEStronglyMeasurable u (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ U))) :
    AEStronglyMeasurable (fun z => ∫ s in (0 : ℝ)..h, u (z.1 + s, z.2))
      (volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ U)) := by
  have hj := (c18_aeStronglyMeasurable_forward_joint hU hhsmall hu).prod_swap
  simpa only [intervalIntegral.integral_of_le hh, Prod.swap] using hj.integral_prod_right'

/-- Forward averaging preserves square integrability on the smaller cylinder. -/
theorem c18_memLp_forward_average {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {d : ℕ} {h : ℝ}
    {U : Set (EinsteinRelation.Vec d)} (hU : MeasurableSet U)
    (hh : 0 < h) (hhsmall : h ≤ 1 / 4)
    [IsFiniteMeasure (volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ U))]
    {u : ℝ × EinsteinRelation.Vec d → E}
    (hu : MemLp u 2 (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ U))) :
    MemLp (fun z => h⁻¹ • ∫ s in (0 : ℝ)..h, u (z.1 + s, z.2)) 2
      (volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ U)) := by
  have hm := (c18_aeStronglyMeasurable_forward_integral hU hh.le hhsmall
    hu.aestronglyMeasurable).const_smul h⁻¹
  apply (memLp_two_iff_integrable_sq_norm hm).2
  have hshift := (c18_memLp_forward_joint hU hhsmall hu).integrable (by norm_num)
  have hsquare := c18_forward_shift_norm_sq_integrable hU hh.le hhsmall hu
  apply (hsquare.2.const_mul h⁻¹).mono_nonneg (hm.norm.pow 2)
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)
  filter_upwards [hshift.prod_left_ae, hsquare.1] with z hz hz2
  exact c18_forward_average_norm_sq_le hh (fun s => u (z.1 + s, z.2)) hz hz2

/-- The coordinate supremum norm is bounded by the explicit Euclidean norm. -/
theorem c18_norm_le_euclideanNorm {d : ℕ} (v : EinsteinRelation.Vec d) :
    ‖v‖ ≤ EinsteinRelation.euclideanNorm v := by
  apply pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _) |>.mpr
  intro i
  exact EinsteinRelation.Regeneration.coordinate_abs_le_euclideanNorm v i

/-- Weighted caloricity controls the gradient in the coordinate norm as well. -/
theorem c18_weighted_caloric_gradient_memLp {d : ℕ} {I : Set ℝ}
    {U : Set (EinsteinRelation.Vec d)} (ρ : EinsteinRelation.Vec d → ℝ)
    (α : EinsteinRelation.Vec d → EinsteinRelation.Mat d)
    (u : ℝ × EinsteinRelation.Vec d → ℝ)
    (G : ℝ × EinsteinRelation.Vec d → EinsteinRelation.Vec d)
    (hu : EinsteinFull.External.Source.GMP.IsWeightedCaloric ρ α I U u G) :
    MemLp G 2 (volume.restrict (I ×ˢ U)) := by
  exact hu.2.2.1.mono' hu.2.1 (Filter.Eventually.of_forall fun z => c18_norm_le_euclideanNorm (G z))

/-- Source balls are measurable in the coordinate-space Borel structure. -/
theorem c18_sourceBall_measurable {d : ℕ} (y : EinsteinRelation.Vec d) (r : ℝ) :
    MeasurableSet (EinsteinFull.External.Source.GMP.sourceBall y r) := by
  have hsum : Continuous (fun v : EinsteinRelation.Vec d => ∑ j, v j * v j) :=
    continuous_finset_sum Finset.univ fun j _ => (continuous_apply j).mul (continuous_apply j)
  have hnorm : Continuous (fun v : EinsteinRelation.Vec d => EinsteinRelation.euclideanNorm v) := by
    unfold EinsteinRelation.euclideanNorm EinsteinRelation.euclideanSq EinsteinRelation.dot
    exact Real.continuous_sqrt.comp hsum
  exact (isOpen_lt (hnorm.comp (continuous_id.sub continuous_const)) continuous_const).measurableSet

/-- Every Euclidean source ball has finite Lebesgue measure. -/
theorem c18_sourceBall_measure_ne_top {d : ℕ} (y : EinsteinRelation.Vec d) (r : ℝ) :
    volume (EinsteinFull.External.Source.GMP.sourceBall y r) ≠ ⊤ := by
  apply ne_top_of_le_ne_top
    (measure_ball_lt_top (μ := (volume : Measure (EinsteinRelation.Vec d))) (x := y) (r := r)).ne
  apply measure_mono
  intro x hx
  change EinsteinRelation.euclideanNorm (x - y) < r at hx
  rw [Metric.mem_ball, dist_eq_norm]
  exact lt_of_le_of_lt (c18_norm_le_euclideanNorm (x - y)) hx

/-- The original source cylinder has finite measure. -/
theorem c18_sourceCylinder_isFiniteMeasure {d : ℕ} (y : EinsteinRelation.Vec d) (r : ℝ) :
    IsFiniteMeasure (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ
      EinsteinFull.External.Source.GMP.sourceBall y r)) := by
  let U := EinsteinFull.External.Source.GMP.sourceBall y r
  letI : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr
    (c18_sourceBall_measure_ne_top y r)
  have hf : IsFiniteMeasure ((volume.restrict (Set.Ioo (-1 : ℝ) 1)).prod
      (volume.restrict U)) := inferInstance
  rw [Measure.prod_restrict] at hf
  exact hf

/-- The smaller source cylinder also has finite measure. -/
theorem c18_smallSourceCylinder_isFiniteMeasure {d : ℕ} (y : EinsteinRelation.Vec d) (r : ℝ) :
    IsFiniteMeasure (volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
      EinsteinFull.External.Source.GMP.sourceBall y r)) := by
  let U := EinsteinFull.External.Source.GMP.sourceBall y r
  letI : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr
    (c18_sourceBall_measure_ne_top y r)
  have hf : IsFiniteMeasure ((volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2))).prod
      (volume.restrict U)) := inferInstance
  rw [Measure.prod_restrict] at hf
  exact hf

/-- Forward averages of a weighted solution and its gradient retain the
square-integrability clauses with the explicit Euclidean gradient norm. -/
theorem c18_weighted_caloric_forward_average_memLp {d : ℕ} {h r : ℝ}
    (hh : 0 < h) (hhsmall : h ≤ 1 / 4) (ρ : EinsteinRelation.Vec d → ℝ)
    (α : EinsteinRelation.Vec d → EinsteinRelation.Mat d) (y : EinsteinRelation.Vec d)
    (u : ℝ × EinsteinRelation.Vec d → ℝ)
    (G : ℝ × EinsteinRelation.Vec d → EinsteinRelation.Vec d)
    (hu : EinsteinFull.External.Source.GMP.IsWeightedCaloric ρ α (Set.Ioo (-1) 1)
      (EinsteinFull.External.Source.GMP.sourceBall y r) u G) :
    MemLp (fun z => h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1 + s, z.2)) 2
      (volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
        EinsteinFull.External.Source.GMP.sourceBall y r)) ∧
    MemLp (fun z => EinsteinRelation.euclideanNorm
      (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1 + s, z.2))) 2
      (volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
        EinsteinFull.External.Source.GMP.sourceBall y r)) := by
  letI := c18_smallSourceCylinder_isFiniteMeasure y r
  have hG := c18_memLp_forward_average (c18_sourceBall_measurable y r) hh hhsmall
    (c18_weighted_caloric_gradient_memLp ρ α u G hu)
  have hsum : Continuous (fun v : EinsteinRelation.Vec d => ∑ j, v j * v j) :=
    continuous_finset_sum Finset.univ fun j _ => (continuous_apply j).mul (continuous_apply j)
  have hnorm : Continuous (fun v : EinsteinRelation.Vec d => EinsteinRelation.euclideanNorm v) := by
    unfold EinsteinRelation.euclideanNorm EinsteinRelation.euclideanSq EinsteinRelation.dot
    exact Real.continuous_sqrt.comp hsum
  refine ⟨?_, ?_⟩
  · simpa only [smul_eq_mul] using c18_memLp_forward_average
      (c18_sourceBall_measurable y r) hh hhsmall hu.1
  · apply (hG.norm.const_mul ((d : ℝ) + 1)).mono'
      (hnorm.comp_aestronglyMeasurable hG.aestronglyMeasurable)
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ EinsteinRelation.euclideanNorm
      (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1 + s, z.2)) from Real.sqrt_nonneg _)]
    exact EinsteinRelation.euclideanNorm_le_dimension_mul_norm
      (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1 + s, z.2))

/-- Almost every time slice of the forward solution and gradient averages is
integrable over the source ball. -/
theorem c18_weighted_caloric_forward_average_ae_integrable {d : ℕ} {h r : ℝ}
    (hh : 0 < h) (hhsmall : h ≤ 1 / 4) (ρ : EinsteinRelation.Vec d → ℝ)
    (α : EinsteinRelation.Vec d → EinsteinRelation.Mat d) (y : EinsteinRelation.Vec d)
    (u : ℝ × EinsteinRelation.Vec d → ℝ)
    (G : ℝ × EinsteinRelation.Vec d → EinsteinRelation.Vec d)
    (hu : EinsteinFull.External.Source.GMP.IsWeightedCaloric ρ α (Set.Ioo (-1) 1)
      (EinsteinFull.External.Source.GMP.sourceBall y r) u G) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)),
      Integrable (fun x => h⁻¹ * ∫ s in (0 : ℝ)..h, u (t + s, x))
        (volume.restrict (EinsteinFull.External.Source.GMP.sourceBall y r)) ∧
      Integrable (fun x => h⁻¹ • ∫ s in (0 : ℝ)..h, G (t + s, x))
        (volume.restrict (EinsteinFull.External.Source.GMP.sourceBall y r)) := by
  letI := c18_smallSourceCylinder_isFiniteMeasure y r
  have hU := (c18_weighted_caloric_forward_average_memLp hh hhsmall ρ α y u G hu).1.integrable
    (by norm_num)
  have hG := (c18_memLp_forward_average (c18_sourceBall_measurable y r) hh hhsmall
    (c18_weighted_caloric_gradient_memLp ρ α u G hu)).integrable (by norm_num)
  have hU' : Integrable (fun z => h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1 + s, z.2))
      ((volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2))).prod
        (volume.restrict (EinsteinFull.External.Source.GMP.sourceBall y r))) := by
    rw [Measure.prod_restrict]
    exact hU
  have hG' : Integrable (fun z => h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1 + s, z.2))
      ((volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2))).prod
        (volume.restrict (EinsteinFull.External.Source.GMP.sourceBall y r))) := by
    rw [Measure.prod_restrict]
    exact hG
  filter_upwards [hU'.prod_right_ae, hG'.prod_right_ae] with t ht htG
  exact ⟨ht, htG⟩

/-- Averaged solution slices and all coordinates of averaged gradient slices
are locally integrable on the original spatial domain. -/
theorem c18_weighted_caloric_forward_average_ae_locallyIntegrable {d : ℕ} {h r : ℝ}
    (hh : 0 < h) (hhsmall : h ≤ 1 / 4) (ρ : EinsteinRelation.Vec d → ℝ)
    (α : EinsteinRelation.Vec d → EinsteinRelation.Mat d) (y : EinsteinRelation.Vec d)
    (u : ℝ × EinsteinRelation.Vec d → ℝ)
    (G : ℝ × EinsteinRelation.Vec d → EinsteinRelation.Vec d)
    (hu : EinsteinFull.External.Source.GMP.IsWeightedCaloric ρ α (Set.Ioo (-1) 1)
      (EinsteinFull.External.Source.GMP.sourceBall y r) u G) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)),
      LocallyIntegrableOn (fun x => h⁻¹ * ∫ s in (0 : ℝ)..h, u (t + s, x))
        (EinsteinFull.External.Source.GMP.sourceBall y r) volume ∧
      ∀ i : Fin d, LocallyIntegrableOn
        (fun x => (h⁻¹ • ∫ s in (0 : ℝ)..h, G (t + s, x)) i)
        (EinsteinFull.External.Source.GMP.sourceBall y r) volume := by
  filter_upwards [c18_weighted_caloric_forward_average_ae_integrable hh hhsmall ρ α y u G hu]
    with t ht
  refine ⟨IntegrableOn.locallyIntegrableOn ht.1, ?_⟩
  intro i
  exact IntegrableOn.locallyIntegrableOn (ht.2.eval i)

/-- Joint forward shifts of a weighted solution and its gradient are integrable,
so Fubini applies on the finite shift interval and smaller source cylinder. -/
theorem c18_weighted_caloric_forward_joint_integrable {d : ℕ} {h r : ℝ}
    (hhsmall : h ≤ 1 / 4) (ρ : EinsteinRelation.Vec d → ℝ)
    (α : EinsteinRelation.Vec d → EinsteinRelation.Mat d) (y : EinsteinRelation.Vec d)
    (u : ℝ × EinsteinRelation.Vec d → ℝ)
    (G : ℝ × EinsteinRelation.Vec d → EinsteinRelation.Vec d)
    (hu : EinsteinFull.External.Source.GMP.IsWeightedCaloric ρ α (Set.Ioo (-1) 1)
      (EinsteinFull.External.Source.GMP.sourceBall y r) u G) :
    Integrable (fun p : ℝ × (ℝ × EinsteinRelation.Vec d) => u (p.2.1 + p.1, p.2.2))
      ((volume.restrict (Set.Ioc (0 : ℝ) h)).prod
        (volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
          EinsteinFull.External.Source.GMP.sourceBall y r))) ∧
    Integrable (fun p : ℝ × (ℝ × EinsteinRelation.Vec d) => G (p.2.1 + p.1, p.2.2))
      ((volume.restrict (Set.Ioc (0 : ℝ) h)).prod
        (volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
          EinsteinFull.External.Source.GMP.sourceBall y r))) := by
  letI := c18_smallSourceCylinder_isFiniteMeasure y r
  exact ⟨(c18_memLp_forward_joint (c18_sourceBall_measurable y r) hhsmall hu.1).integrable
      (by norm_num),
    (c18_memLp_forward_joint (c18_sourceBall_measurable y r) hhsmall
      (c18_weighted_caloric_gradient_memLp ρ α u G hu)).integrable (by norm_num)⟩

/-- Joint shift integrability gives the Fubini integrability needed on almost
every spatial time slice. -/
theorem c18_forward_joint_ae_integrable_slice {E : Type*} [NormedAddCommGroup E]
    {d : ℕ} {h : ℝ} {U : Set (EinsteinRelation.Vec d)}
    {f : ℝ × EinsteinRelation.Vec d → E}
    (hf : Integrable (fun p : ℝ × (ℝ × EinsteinRelation.Vec d) =>
        f (p.2.1 + p.1, p.2.2))
      ((volume.restrict (Set.Ioc (0 : ℝ) h)).prod
        (volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ U)))) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)),
      Integrable (fun p : ℝ × EinsteinRelation.Vec d => f (t + p.1, p.2))
        ((volume.restrict (Set.Ioc (0 : ℝ) h)).prod (volume.restrict U)) := by
  let μt := (volume : Measure ℝ).restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2))
  let μs := (volume : Measure ℝ).restrict (Set.Ioc 0 h)
  let μx := (volume : Measure (EinsteinRelation.Vec d)).restrict U
  have hf' : Integrable (fun p : (ℝ × EinsteinRelation.Vec d) × ℝ =>
      f (p.1.1 + p.2, p.1.2)) ((μt.prod μx).prod μs) := by
    simpa [μt, μs, μx, ← Measure.volume_eq_prod ℝ (EinsteinRelation.Vec d),
      Measure.prod_restrict, Function.comp_def] using hf.swap
  have hp := (measurePreserving_prodAssoc μt μx μs).symm.integrable_comp_of_integrable hf'
  have hp' : Integrable (fun p : ℝ × (EinsteinRelation.Vec d × ℝ) =>
      f (p.1 + p.2.2, p.2.1)) (μt.prod (μx.prod μs)) := by
    exact hp
  filter_upwards [hp'.prod_right_ae] with t ht
  exact ht.swap

/-- Almost every small-cylinder time slice has Fubini-integrable shifted data,
and the shifted gradient identity holds for almost every forward shift. -/
theorem c18_weighted_caloric_forward_ae_slice_data {d : ℕ} {h r : ℝ}
    (hhsmall : h ≤ 1 / 4) (ρ : EinsteinRelation.Vec d → ℝ)
    (α : EinsteinRelation.Vec d → EinsteinRelation.Mat d) (y : EinsteinRelation.Vec d)
    (u : ℝ × EinsteinRelation.Vec d → ℝ)
    (G : ℝ × EinsteinRelation.Vec d → EinsteinRelation.Vec d)
    (hu : EinsteinFull.External.Source.GMP.IsWeightedCaloric ρ α (Set.Ioo (-1) 1)
      (EinsteinFull.External.Source.GMP.sourceBall y r) u G) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)),
      Integrable (fun p : ℝ × EinsteinRelation.Vec d => u (t + p.1, p.2))
        ((volume.restrict (Set.Ioc (0 : ℝ) h)).prod
          (volume.restrict (EinsteinFull.External.Source.GMP.sourceBall y r))) ∧
      Integrable (fun p : ℝ × EinsteinRelation.Vec d => G (t + p.1, p.2))
        ((volume.restrict (Set.Ioc (0 : ℝ) h)).prod
          (volume.restrict (EinsteinFull.External.Source.GMP.sourceBall y r))) ∧
      ∀ᵐ s ∂volume.restrict (Set.Ioc (0 : ℝ) h),
        EinsteinRelation.HasWeakGradient (EinsteinFull.External.Source.GMP.sourceBall y r)
          (fun x => u (t + s, x)) (fun x => G (t + s, x)) := by
  have hj := c18_weighted_caloric_forward_joint_integrable hhsmall ρ α y u G hu
  filter_upwards [c18_forward_joint_ae_integrable_slice hj.1,
    c18_forward_joint_ae_integrable_slice hj.2,
    c18_weighted_caloric_ae_shifted_gradient hhsmall ρ α y u G hu] with t hU hG hgrad
  exact ⟨hU, hG, hgrad⟩

/-- The forward averages of the actual weighted solution and gradient are
almost-everywhere strongly measurable on the smaller cylinder. -/
theorem c18_weighted_caloric_forward_integrals_measurable {d : ℕ} {h r : ℝ}
    (hh : 0 ≤ h) (hhsmall : h ≤ 1 / 4) (ρ : EinsteinRelation.Vec d → ℝ)
    (α : EinsteinRelation.Vec d → EinsteinRelation.Mat d) (y : EinsteinRelation.Vec d)
    (u : ℝ × EinsteinRelation.Vec d → ℝ)
    (G : ℝ × EinsteinRelation.Vec d → EinsteinRelation.Vec d)
    (hu : EinsteinFull.External.Source.GMP.IsWeightedCaloric ρ α (Set.Ioo (-1) 1)
      (EinsteinFull.External.Source.GMP.sourceBall y r) u G) :
    AEStronglyMeasurable (fun z => ∫ s in (0 : ℝ)..h, u (z.1 + s, z.2))
      (volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
        EinsteinFull.External.Source.GMP.sourceBall y r)) ∧
    AEStronglyMeasurable (fun z => ∫ s in (0 : ℝ)..h, G (z.1 + s, z.2))
      (volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
        EinsteinFull.External.Source.GMP.sourceBall y r)) := by
  exact ⟨c18_aeStronglyMeasurable_forward_integral (c18_sourceBall_measurable y r)
      hh hhsmall hu.1.aestronglyMeasurable,
    c18_aeStronglyMeasurable_forward_integral (c18_sourceBall_measurable y r)
      hh hhsmall hu.2.1⟩

/-- The actual weighted solution and gradient have forward time integrals at
almost every spatial point, simultaneously for every permitted starting time. -/
theorem c18_weighted_caloric_ae_intervalIntegrable_forward {d : ℕ} {h r : ℝ}
    (hh : 0 ≤ h) (hhsmall : h ≤ 1 / 4) (ρ : EinsteinRelation.Vec d → ℝ)
    (α : EinsteinRelation.Vec d → EinsteinRelation.Mat d) (y : EinsteinRelation.Vec d)
    (u : ℝ × EinsteinRelation.Vec d → ℝ)
    (G : ℝ × EinsteinRelation.Vec d → EinsteinRelation.Vec d)
    (hu : EinsteinFull.External.Source.GMP.IsWeightedCaloric ρ α (Set.Ioo (-1) 1)
      (EinsteinFull.External.Source.GMP.sourceBall y r) u G) :
    ∀ᵐ x ∂volume.restrict (EinsteinFull.External.Source.GMP.sourceBall y r),
      ∀ t ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2),
        IntervalIntegrable (fun s => u (t + s, x)) volume 0 h ∧
        IntervalIntegrable (fun s => G (t + s, x)) volume 0 h := by
  letI := c18_sourceCylinder_isFiniteMeasure y r
  have hu' := c18_ae_intervalIntegrable_forward_of_memLp hh hhsmall hu.1
  have hG' := c18_ae_intervalIntegrable_forward_of_memLp hh hhsmall
    (c18_weighted_caloric_gradient_memLp ρ α u G hu)
  filter_upwards [hu', hG'] with x hx hGx t ht
  exact ⟨hx t ht, hGx t ht⟩

/-- A time average has the finite-difference increment needed in the weighted
chain rule, for any locally integrable time slice. -/
theorem c18_forward_integral_increment {f : ℝ → ℝ} {a b h : ℝ}
    (ha : IntervalIntegrable f volume a (a + h))
    (hb : IntervalIntegrable f volume b (b + h))
    (hab : IntervalIntegrable f volume a b) :
    (∫ s in (0 : ℝ)..h, f (b + s)) - (∫ s in (0 : ℝ)..h, f (a + s)) =
      ∫ t in a..b, (f (t + h) - f t) := by
  rw [show (fun s : ℝ => f (b + s)) = (fun s => f (s + b)) by
        funext s; rw [add_comm],
      show (fun s : ℝ => f (a + s)) = (fun s => f (s + a)) by
        funext s; rw [add_comm],
      intervalIntegral.integral_comp_add_right, intervalIntegral.integral_comp_add_right]
  simp only [zero_add, add_comm h]
  rw [intervalIntegral.integral_sub
    ((IntervalIntegrable.comp_add_right_iff).mpr (ha.symm.trans (hab.trans hb))) hab,
    intervalIntegral.integral_comp_add_right]
  have heq := intervalIntegral.integral_interval_sub_interval_comm hb ha hab.symm
  rw [intervalIntegral.integral_symm a b, intervalIntegral.integral_symm (a + h) (b + h)] at heq
  linarith

/-- The actual density-weighted forward average has the time increment required
by the weighted chain rule. The density is fixed in time, and no division by it
is involved. -/
theorem c18_weighted_forward_integral_increment {f : ℝ → ℝ} {a b h ρ : ℝ}
    (ha : IntervalIntegrable f volume a (a + h))
    (hb : IntervalIntegrable f volume b (b + h))
    (hab : IntervalIntegrable f volume a b) :
    ρ * (h⁻¹ * (∫ s in (0 : ℝ)..h, f (b + s))) -
      ρ * (h⁻¹ * (∫ s in (0 : ℝ)..h, f (a + s))) =
      ∫ t in a..b, ρ * (h⁻¹ * (f (t + h) - f t)) := by
  simp only [intervalIntegral.integral_const_mul]
  rw [← c18_forward_integral_increment ha hb hab]
  ring

/-- Integrating spatial weak-gradient identities over a finite time measure
commutes with the spatial test pairings. -/
theorem c18_integral_weak_gradient_test {d : ℕ} {U : Set (EinsteinRelation.Vec d)}
    (μ : Measure ℝ) [SFinite μ] (f : ℝ × EinsteinRelation.Vec d → ℝ)
    (g : ℝ × EinsteinRelation.Vec d → EinsteinRelation.Vec d)
    (hf : Integrable f (μ.prod (volume.restrict U)))
    (hg : Integrable g (μ.prod (volume.restrict U)))
    (hweak : ∀ᵐ s ∂μ, EinsteinRelation.HasWeakGradient U (fun x => f (s, x))
      (fun x => g (s, x)))
    (i : Fin d) (φ : EinsteinRelation.Vec d → ℝ)
    (hφ : EinsteinRelation.IsSpatialTest U φ) :
    (∫ x in U, (∫ s, f (s, x) ∂μ) * EinsteinRelation.coordinateDerivative i φ x) =
      -(∫ x in U, (∫ s, g (s, x) ∂μ) i * φ x) := by
  let ν := (volume : Measure (EinsteinRelation.Vec d)).restrict U
  let P := μ.prod ν
  have hφtop : MemLp (fun p : ℝ × EinsteinRelation.Vec d => φ p.2) ⊤ P := by
    have ht := hφ.1.continuous.memLp_top_of_hasCompactSupport hφ.2.1 (Measure.map Prod.snd P)
    exact ht.comp_of_map measurable_snd.aemeasurable
  have hdtop : MemLp (fun p : ℝ × EinsteinRelation.Vec d =>
      EinsteinRelation.coordinateDerivative i φ p.2) ⊤ P := by
    have ht := ((hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_top_of_hasCompactSupport
      (hφ.2.1.fderiv_apply ℝ (EinsteinRelation.unitVector i)) (Measure.map Prod.snd P)
    exact ht.comp_of_map measurable_snd.aemeasurable
  have hleft : Integrable (fun p : ℝ × EinsteinRelation.Vec d =>
      f p * EinsteinRelation.coordinateDerivative i φ p.2) P :=
    memLp_one_iff_integrable.mp ((memLp_one_iff_integrable.mpr hf).mul hdtop)
  have hright : Integrable (fun p : ℝ × EinsteinRelation.Vec d => g p i * φ p.2) P :=
    memLp_one_iff_integrable.mp ((memLp_one_iff_integrable.mpr (hg.eval i)).mul hφtop)
  have htest : (∫ s, (∫ x in U, f (s, x) * EinsteinRelation.coordinateDerivative i φ x) ∂μ) =
      -(∫ s, (∫ x in U, g (s, x) i * φ x) ∂μ) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [hweak] with s hs
    exact (hs i).2.2 φ hφ
  have hleft_eq : (∫ x in U, (∫ s, f (s, x) ∂μ) * EinsteinRelation.coordinateDerivative i φ x) =
      ∫ x in U, ∫ s, f (s, x) * EinsteinRelation.coordinateDerivative i φ x ∂μ := by
    apply integral_congr_ae
    filter_upwards [] with x
    rw [integral_mul_const]
  have hright_eq : (∫ x in U, (∫ s, g (s, x) ∂μ) i * φ x) =
      ∫ x in U, ∫ s, g (s, x) i * φ x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hg.swap.prod_right_ae] with x hx
    rw [integral_mul_const]
    congr 1
    exact ((ContinuousLinearMap.proj i : EinsteinRelation.Vec d →L[ℝ] ℝ).integral_comp_comm hx).symm
  rw [hleft_eq, hright_eq]
  calc
    _ = ∫ s, (∫ x in U, f (s, x) * EinsteinRelation.coordinateDerivative i φ x) ∂μ :=
      (integral_integral_swap hleft).symm
    _ = -(∫ s, (∫ x in U, g (s, x) i * φ x) ∂μ) := htest
    _ = _ := congrArg Neg.neg (integral_integral_swap hright)

/-- Forward averages retain the actual spatial weak gradient on almost every
smaller-cylinder time slice. -/
theorem c18_weighted_caloric_forward_average_ae_weakGradient {d : ℕ} {h r : ℝ}
    (hh : 0 < h) (hhsmall : h ≤ 1 / 4) (ρ : EinsteinRelation.Vec d → ℝ)
    (α : EinsteinRelation.Vec d → EinsteinRelation.Mat d) (y : EinsteinRelation.Vec d)
    (u : ℝ × EinsteinRelation.Vec d → ℝ)
    (G : ℝ × EinsteinRelation.Vec d → EinsteinRelation.Vec d)
    (hu : EinsteinFull.External.Source.GMP.IsWeightedCaloric ρ α (Set.Ioo (-1) 1)
      (EinsteinFull.External.Source.GMP.sourceBall y r) u G) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)),
      EinsteinRelation.HasWeakGradient (EinsteinFull.External.Source.GMP.sourceBall y r)
        (fun x => h⁻¹ * ∫ s in (0 : ℝ)..h, u (t + s, x))
        (fun x => h⁻¹ • ∫ s in (0 : ℝ)..h, G (t + s, x)) := by
  filter_upwards [c18_weighted_caloric_forward_ae_slice_data hhsmall ρ α y u G hu,
    c18_weighted_caloric_forward_average_ae_locallyIntegrable hh hhsmall ρ α y u G hu]
    with t ht hlocal
  intro i
  refine ⟨hlocal.1, hlocal.2 i, ?_⟩
  intro φ hφ
  have htst := c18_integral_weak_gradient_test (volume.restrict (Set.Ioc (0 : ℝ) h))
    (fun p => u (t + p.1, p.2)) (fun p => G (t + p.1, p.2)) ht.1 ht.2.1 ht.2.2 i φ hφ
  simp only [intervalIntegral.integral_of_le hh.le, Pi.smul_apply, smul_eq_mul]
  have hl : (∫ x in EinsteinFull.External.Source.GMP.sourceBall y r,
      (h⁻¹ * ∫ s in Set.Ioc (0 : ℝ) h, u (t + s, x)) *
        EinsteinRelation.coordinateDerivative i φ x) =
      h⁻¹ * ∫ x in EinsteinFull.External.Source.GMP.sourceBall y r,
        (∫ s in Set.Ioc (0 : ℝ) h, u (t + s, x)) *
          EinsteinRelation.coordinateDerivative i φ x := by
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  have hr : (∫ x in EinsteinFull.External.Source.GMP.sourceBall y r,
      (h⁻¹ * (∫ s in Set.Ioc (0 : ℝ) h, G (t + s, x)) i) * φ x) =
      h⁻¹ * ∫ x in EinsteinFull.External.Source.GMP.sourceBall y r,
        (∫ s in Set.Ioc (0 : ℝ) h, G (t + s, x)) i * φ x := by
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  rw [hl, hr, htst]
  ring

end EinsteinFull.Calculus
