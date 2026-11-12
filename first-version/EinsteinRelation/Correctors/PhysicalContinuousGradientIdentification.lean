import EinsteinRelation.Correctors.CanonicalContinuousGradientIdentification
import EinsteinRelation.Correctors.RecenteredPhysicalCopies

/-! # Continuous canonical gradients directly on the physical law

Source: `paper/main.tex:860–875,886–894`. A continuous physical version is
identified at each fixed point using stationarity and Fubini. No extension
of that version away from the physical reduction image is required.
-/

open MeasureTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors
open External.AKM ReductionImageV3 Environment.AKMTestIntegralSupport
open NormalizedSpatialRepresentativeSupport

attribute [local instance] ReductionImageV3.fieldPair_standardBorel
local instance physicalGradientRestrictionMeasurableSpace {d : ℕ} (U : Set (Vec d)) :
    MeasurableSpace C(U, Mat d) := borel C(U, Mat d)

/-- Spatial a.e. identification determines every fixed point of a jointly
measurable continuous physical version, almost surely in the physical law.
Source: `paper/main.tex:860–875`. -/
theorem ae_physical_continuous_version_eq_conditionalCorrectorGradient
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (g : PhysicalField d L → Vec d → Vec d)
    (hm : Measurable (fun z : PhysicalField d L × Vec d => g z.1 z.2))
    (hc : ∀ᵐ ω ∂physicalReferenceLaw Q, Continuous (g ω))
    (hid : ∀ᵐ ω ∂physicalReferenceLaw Q,
      g ω =ᵐ[volume] fun x =>
        conditionalCorrectorGradient Q i (WithLp.toLp 2 x) (reduce ω.1))
    (y : Point d) :
    (fun ω => g ω y.ofLp) =ᵐ[physicalReferenceLaw Q]
      fun ω => conditionalCorrectorGradient Q i y (reduce ω.1) := by
  let P := physicalReferenceLaw Q
  letI : IsProbabilityMeasure P := physicalReferenceLaw_probability Q
  let F : PhysicalField d L → Vec d := fun ω => conditionalCorrectorGradient Q i 0 (reduce ω.1)
  have hgrad : Measurable (conditionalCorrectorGradient Q i 0) :=
    (PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin d => ℝ)).measurable.comp
      ((Lp.stronglyMeasurable (canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))).measurable.comp
          (Probability.measurable_translate 0))
  have hFm : Measurable F := hgrad.comp (measurePreserving_physicalReduction Q).measurable
  have hmp (x : Vec d) : MeasurePreserving (physicalTranslate x) P P :=
    ⟨measurable_physicalTranslate _,physicalReferenceLaw_translation_invariant Q _⟩
  have hTm : Measurable (fun z : PhysicalField d L × Vec d =>
      physicalTranslate z.2 z.1) :=
    (Probability.continuous_translate.measurable.comp
      (measurable_snd.prodMk (measurable_subtype_coe.comp measurable_fst))).subtype_mk
  have hid' : ∀ᵐ ω ∂P, g ω =ᵐ[volume] fun x => F (physicalTranslate x ω) := by
    simpa only [F,conditionalCorrectorGradient,StationarySpatialRealization.spatialRealization,
      WithLp.ofLp_toLp,WithLp.ofLp_zero,translate_zero,physicalTranslate,reduce_translate]
      using hid
  have hpoint (x : Vec d) : ∀ᵐ ω ∂P, g ω x = g (physicalTranslate x ω) 0 := by
    have hcov := ae_spatial_covariance_congr P (physicalTranslate x) (hmp x) x g
      (fun ω z => F (physicalTranslate z ω)) hid'
      (ae_of_all _ fun ω => ae_of_all _ fun z => by
        apply congrArg F
        apply Subtype.ext
        exact (translate_add z x ω.1).symm)
    filter_upwards [hcov,hc,(hmp x).quasiMeasurePreserving.ae hc] with ω hω hcω hcx
    have he := Measure.eq_of_ae_eq hω (hcω.comp (continuous_id.add continuous_const)) hcx
    simpa only [zero_add] using congrFun he 0
  have hjoint : MeasurableSet {z : PhysicalField d L × Vec d |
      g z.1 z.2 = g (physicalTranslate z.2 z.1) 0} :=
    measurableSet_eq_fun hm (hm.comp (hTm.prodMk measurable_const))
  have hsp : ∀ᵐ ω ∂P, ∀ᵐ x ∂(volume : Measure (Vec d)),
      g (physicalTranslate x ω) 0 = F (physicalTranslate x ω) := by
    have hx := (Measure.ae_ae_comm (μ := P) (ν := (volume : Measure (Vec d))) hjoint).mpr
      (Filter.Eventually.of_forall hpoint)
    filter_upwards [hx,hid'] with ω hxω hiω
    filter_upwards [hxω,hiω] with x hx hi
    exact hx.symm.trans hi
  have hset : MeasurableSet {z : PhysicalField d L × Vec d |
      g (physicalTranslate z.2 z.1) 0 = F (physicalTranslate z.2 z.1)} :=
    measurableSet_eq_fun (hm.comp (hTm.prodMk measurable_const)) (hFm.comp hTm)
  obtain ⟨x,hx⟩ := ((Measure.ae_ae_comm hset).mp hsp).exists
  have hzero : (fun ω => g ω 0) =ᵐ[P] F := by
    filter_upwards [(hmp (-x)).quasiMeasurePreserving.ae hx] with ω hω
    have ht : physicalTranslate x (physicalTranslate (-x) ω) = ω := by
      apply Subtype.ext
      simp only [physicalTranslate, translate_add, add_neg_cancel, translate_zero]
    simpa only [ht] using hω
  filter_upwards [hpoint y.ofLp,(hmp y.ofLp).quasiMeasurePreserving.ae hzero] with ω hp hz
  exact hp.trans (by simpa only [F,conditionalCorrectorGradient,
    StationarySpatialRealization.spatialRealization,WithLp.ofLp_zero,
    translate_zero,physicalTranslate,reduce_translate] using hz)

/-- The production point-gradient copy norm is exactly the origin norm of
any identified continuous physical version under the actual recentered
physical coupling. Source: `paper/main.tex:861–875,886–894`. -/
theorem eLpNorm_conditionalCopy_gradient_eq_physical_continuous_version
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (g : PhysicalField d L → Vec d → Vec d)
    (hm : Measurable (fun z : PhysicalField d L × Vec d => g z.1 z.2))
    (hc : ∀ᵐ ω ∂physicalReferenceLaw Q, Continuous (g ω))
    (hid : ∀ᵐ ω ∂physicalReferenceLaw Q,
      g ω =ᵐ[volume] fun x =>
        conditionalCorrectorGradient Q i (WithLp.toLp 2 x) (reduce ω.1))
    (R : ℝ) (y : Point d) (p : ℝ≥0∞) :
    eLpNorm (fun z : C(conditionalCorrectorBall R y, Mat d) ×
      (FieldPair d × FieldPair d) => euclideanNorm
        (conditionalCorrectorGradient Q i y z.2.1 - conditionalCorrectorGradient Q i y z.2.2))
      p (reducedConditionalCopyLaw (reducedEnvironmentLaw Q) (conditionalCorrectorBall R y)) =
    eLpNorm (fun z : PhysicalField d L × PhysicalField d L =>
      euclideanNorm (g z.1 0 - g z.2 0)) p (recenteredPhysicalCopyLaw Q R y) := by
  rw [eLpNorm_conditionalCorrectorGradient_eq_recentered]
  obtain ⟨_,hred,hfst,hsnd,_⟩ := recenteredPhysicalCopy_properties Q R y
  have hgrad : Measurable (conditionalCorrectorGradient Q i 0) :=
    (PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin d => ℝ)).measurable.comp
      ((Lp.stronglyMeasurable (canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))).measurable.comp
          (Probability.measurable_translate 0))
  have hnorm : Measurable (fun z : FieldPair d × FieldPair d => euclideanNorm
      (conditionalCorrectorGradient Q i 0 z.1 - conditionalCorrectorGradient Q i 0 z.2)) := by
    unfold euclideanNorm euclideanSq dot
    fun_prop
  rw [← eLpNorm_comp_measurePreserving hnorm.aestronglyMeasurable hred]
  have hzero := ae_physical_continuous_version_eq_conditionalCorrectorGradient Q i g hm hc hid 0
  simp only [WithLp.ofLp_zero] at hzero
  apply eLpNorm_congr_ae
  filter_upwards [hfst.quasiMeasurePreserving.ae hzero,
    hsnd.quasiMeasurePreserving.ae hzero] with z h₁ h₂
  simp only [Function.comp_def,physicalPairReduction,h₁,h₂]

end EinsteinRelation.Correctors
