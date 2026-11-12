import EinsteinRelation.Correctors.CorrectorMomentsFromLiterature
import EinsteinRelation.Correctors.NormalizedScalarCenteredGauge
import EinsteinRelation.Correctors.NormalizedSourceDominatedMoment
import EinsteinRelation.Correctors.MollifierScaledSpatialMomentComparison
import EinsteinRelation.Correctors.NormalizedScalarMollifierMean
import EinsteinRelation.Correctors.P53SourceSkewScalarPotential
import EinsteinRelation.Correctors.CenteredEuclideanTransport
import EinsteinRelation.Correctors.IntegralMomentNormBound
import EinsteinRelation.Correctors.CoordinateMomentProjections

/-! # Ordinary local source moments on the conditioning ball

Source: `paper/main.tex:715–722,913–925,942–947`. The actual normalized
sources are jointly integrable on the larger ball used for coefficient
conditioning. The scalar normalization radius need not equal the radius
of the moment estimate: its centered values are gauge independent.
-/

open MeasureTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger HeatSelectedSkewMeaning
open NormalizedSpatialRepresentativeSupport NormalizedScalarPhysicalLawTransportSupport

private theorem memLp_of_nested_power_bound {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [SFinite μ] (ν : Measure X) [SFinite ν]
    {p B : ℝ} (hp : 0 < p) (f : Ω → X → ℝ)
    (hf : StronglyMeasurable (Function.uncurry f))
    (hb : (∫⁻ ω, ∫⁻ x, ENNReal.ofReal (|f ω x| ^ p) ∂ν ∂μ) ≤ ENNReal.ofReal B) :
    MemLp (Function.uncurry f) (ENNReal.ofReal p) (μ.prod ν) := by
  have hm : Measurable (fun z : Ω × X => ENNReal.ofReal (|f z.1 z.2| ^ p)) :=
    ((hf.measurable.abs).pow_const p).ennreal_ofReal
  have hb' : (∫⁻ z : Ω × X, ENNReal.ofReal (|f z.1 z.2| ^ p) ∂μ.prod ν) ≤
      ENNReal.ofReal B := by simpa only [lintegral_prod _ hm.aemeasurable] using hb
  have hn := eLpNorm_le_of_lintegral_moment (μ.prod ν) hp
    (fun z => abs_nonneg (f z.1 z.2)) hb'
  have hn' : eLpNorm (Function.uncurry f) (ENNReal.ofReal p) (μ.prod ν) ≤
      ENNReal.ofReal ((max B 0) ^ (1 / p)) := by
    simpa only [← Real.norm_eq_abs, eLpNorm_norm] using hn
  exact ⟨hf.aestronglyMeasurable, hn'.trans_lt ENNReal.ofReal_lt_top⟩

/-- The actual normalized scalar and heat-selected skew sources have
ordinary product-space moments on the entire coefficient-conditioning
ball, conditional only on the existing literature estimates and source
construction. Source: `paper/main.tex:715–722,913–925,942–947`. -/
theorem corrector_sources_conditioning_ball_memLp_of_literature
    (h45 : ScalarStationaryEstimate) (h46 : ScalarPlanarL2Estimate)
    (h47 : ScalarHeatDifferenceEstimate) (h68 : FluxGradientEstimate)
    (h614 : FluxStationaryEstimate) (h615 : FluxPlanarL2Estimate)
    (h616 : FluxHeatDifferenceEstimate) (hP : BallPoincareEstimate)
    (h817 : LocalBoundednessEstimate) (h832 : InteriorGradientEstimate)
    (h836 : InteriorRegularRepresentative)
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ R p : ℝ}
    (hp : 2 ≤ p) (Q : EnvironmentLaw d L r₀) (hR : 1 ≤ R) (i : Fin d)
    (u : FieldPair d → Vec d → ℝ) (S : FieldPair d → Vec d → Mat d)
    (hu : IsNormalizedCanonicalScalarCorrector Q i (canonicalSourceMollifier d) R hR 0
      (fun ω x => u ω x.ofLp))
    (hS : HasHeatSelectedSkewCorrectorColumn (Fact.out : 2 ≤ d) Q i S)
    (hSm : ∀ j k, StronglyMeasurable (fun z : FieldPair d × Vec d => S z.1 z.2 j k))
    (hSzero : ∀ j k, ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      (∫ y, S ω (-y) j k ∂mollifierCenterMeasure d R) = 0) :
    MemLp (Function.uncurry u) (ENNReal.ofReal p)
      ((reducedEnvironmentLaw Q).prod (volume.restrict (ball (0 : Vec d) (32 * R)))) ∧
      ∀ j k, MemLp (fun z : FieldPair d × Vec d => S z.1 z.2 j k) (ENNReal.ofReal p)
        ((reducedEnvironmentLaw Q).prod (volume.restrict (ball (0 : Vec d) (32 * R)))) := by
  let B := ball (0 : Vec d) (32 * R)
  let β : Measure (Vec d) := volume.restrict B
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hr : 0 < 32 * R := by positivity
  have hvol := ENNReal.toReal_pos_iff.mp (paired_ball_volume_pos_finite (d := d) hr)
  letI : IsFiniteMeasure β := isFiniteMeasure_restrict.mpr hvol.2.ne
  letI : NeZero β := ⟨by
    intro h
    have hh : β Set.univ = 0 := by rw [h]; simp
    exact hvol.1.ne' (by simpa only [β, B, Measure.restrict_apply_univ] using hh)⟩
  let γ := (β Set.univ)⁻¹ • β
  letI : IsProbabilityMeasure γ := inferInstance
  letI := isProbabilityMeasure_mollifierCenterMeasure (d := d) hR0
  obtain ⟨D, _, hdom⟩ := exists_mollifierCenterMeasure_le_scaled_ball_average d 32 (by norm_num)
  have hdγ : mollifierCenterMeasure d R ≤ ENNReal.ofReal D • γ := by
    simpa only [γ, β, B, Measure.restrict_apply_univ] using hdom R hR0
  have hpre : (fun x : Vec d => -x) ⁻¹' B = B := by
    ext x
    simp only [B, ball, Set.mem_preimage, Set.mem_setOf_eq, sub_zero, Entropy.euclideanNorm_neg']
  have hnegβ : MeasurePreserving (fun x : Vec d => -x) β β := by
    simpa only [β, hpre] using
      (Measure.measurePreserving_neg (volume : Measure (Vec d))).restrict_preimage_emb
        (MeasurableEquiv.neg (Vec d)).measurableEmbedding B
  have hnegγ : MeasurePreserving (fun x : Vec d => -x) γ γ :=
    ⟨measurable_neg, by dsimp only [γ]; rw [Measure.map_smul, hnegβ.map_eq]⟩
  have hprodneg := (MeasurePreserving.id (reducedEnvironmentLaw Q)).prod hnegγ
  have hum : StronglyMeasurable (Function.uncurry u) := by
    simpa only [Function.uncurry, WithLp.ofLp_toLp] using
      (hu.1.comp measurable_swap).stronglyMeasurable
  have hmneg : Measurable (fun z : FieldPair d × Vec d => (z.1, -z.2)) :=
    measurable_fst.prodMk measurable_snd.neg
  have hT : 1 ≤ 16 * R := by linarith
  obtain ⟨φ, hφ⟩ := exists_normalizedCanonicalScalarCorrector
    hP Q i (canonicalSourceMollifier d) (16 * R) hT 0
  let v : FieldPair d → Vec d → ℝ := fun ω x => φ ω (WithLp.toLp 2 x)
  have hv : IsNormalizedCanonicalScalarCorrector Q i (canonicalSourceMollifier d)
      (16 * R) hT 0 (fun ω x => v ω x.ofLp) := by
    simpa only [v, WithLp.toLp_ofLp] using hφ
  obtain ⟨A, hA⟩ := correctorMoments_of_literature
    h45 h46 h47 h68 h614 h615 h616 hP h817 h832 h836 d L r₀ p hp
  have hpair := (hA Q (canonicalSourceMollifier d)).2
    (16 * R) hT 0 i (fun ω x => v ω x.ofLp) S hv hS
  simp only [centered_scalar_flux_average_toLp, WithLp.ofLp_zero,
    show 2 * (16 * R) = 32 * R by ring] at hpair
  have hceq := ae_centered_normalizedCanonicalScalar_eq Q i
    (canonicalSourceMollifier d) (canonicalSourceMollifier d) hR hT 0 0 u v hu hv (32 * R) hr
  have hcm (w : FieldPair d → Vec d → ℝ) (hw : StronglyMeasurable (Function.uncurry w)) :
      StronglyMeasurable (fun ω => ⨍ z in B, w ω z ∂volume) := by
    simp only [average_eq]
    exact (hw.integral_prod_right' (ν := β)).const_smul ((β.real Set.univ)⁻¹ : ℝ)
  have htransfer (w : FieldPair d → Vec d → ℝ)
      (hw : StronglyMeasurable (Function.uncurry w))
      (hz : ∀ᵐ ω ∂reducedEnvironmentLaw Q,
        (∫ y, w ω (-y) ∂mollifierCenterMeasure d R) = 0)
      (hc : MemLp (fun z : FieldPair d × Vec d => w z.1 z.2 -
        ⨍ a in B, w z.1 a ∂volume) (ENNReal.ofReal p) ((reducedEnvironmentLaw Q).prod γ)) :
      MemLp (Function.uncurry w) (ENNReal.ofReal p) ((reducedEnvironmentLaw Q).prod β) := by
    have hcneg := hc.comp_measurePreserving hprodneg
    have ht := (memLp_normalized_source_of_dominated_centered_moment
      (reducedEnvironmentLaw Q) (mollifierCenterMeasure d R) γ
      (ENNReal.one_le_ofReal.mpr (one_le_two.trans hp)) ENNReal.ofReal_ne_top
      ENNReal.ofReal_ne_top hdγ (fun ω y => w ω (-y)) (hw.comp_measurable hmneg)
      _ (hcm w hw) hz hcneg).1
    have ht' := ht.comp_measurePreserving hprodneg
    have huγ : MemLp (Function.uncurry w) (ENNReal.ofReal p)
        ((reducedEnvironmentLaw Q).prod γ) := by
      convert ht' using 1
      ext z
      change w z.1 z.2 = w z.1 (- -z.2)
      rw [neg_neg]
    have hs := huγ.smul_measure (c := β Set.univ) (measure_ne_top _ _)
    have heq : (β Set.univ) • ((reducedEnvironmentLaw Q).prod γ) =
        (reducedEnvironmentLaw Q).prod β := by
      rw [← Measure.prod_smul_right]
      dsimp only [γ]
      rw [smul_smul, ENNReal.mul_inv_cancel (NeZero.ne (β Set.univ)) (measure_ne_top _ _), one_smul]
    simpa only [heq] using hs
  constructor
  · apply htransfer u hum (normalizedCanonicalScalar_mollifierCenterMean_eq_zero Q i hR u hu)
    apply memLp_of_nested_power_bound (reducedEnvironmentLaw Q) γ (by linarith : 0 < p)
      (fun ω x => u ω x - ⨍ a in B, u ω a ∂volume)
      (hum.sub ((hcm u hum).comp_measurable measurable_fst))
    have heq : (∫⁻ ω, ∫⁻ x, ENNReal.ofReal (|u ω x - ⨍ a in B, u ω a ∂volume| ^ p)
        ∂γ ∂reducedEnvironmentLaw Q) =
        ∫⁻ ω, ∫⁻ x, ENNReal.ofReal (|v ω x - ⨍ a in B, v ω a ∂volume| ^ p)
          ∂γ ∂reducedEnvironmentLaw Q := by
      apply lintegral_congr_ae
      filter_upwards [hceq] with ω hω
      apply lintegral_congr_ae
      filter_upwards [Measure.ae_smul_measure hω (β Set.univ)⁻¹] with x hx
      rw [hx]
    rw [heq]
    exact (lintegral_mono fun _ => lintegral_mono fun _ => le_add_right le_rfl).trans hpair
  · intro j k
    apply htransfer (fun ω x => S ω x j k) (hSm j k) (hSzero j k)
    apply memLp_of_nested_power_bound (reducedEnvironmentLaw Q) γ (by linarith : 0 < p)
      (fun ω x => S ω x j k - ⨍ a in B, S ω a j k ∂volume)
      ((hSm j k).sub ((hcm (fun ω x => S ω x j k) (hSm j k)).comp_measurable measurable_fst))
    refine (lintegral_mono fun ω => lintegral_mono fun x => ?_).trans hpair
    apply (le_add_left le_rfl).trans'
    apply ENNReal.ofReal_le_ofReal
    exact Real.rpow_le_rpow (abs_nonneg _)
      (abs_entry_le_frobeniusNorm (S ω x - Matrix.of (fun a b =>
        ⨍ z in B, S ω z a b ∂volume)) j k) (by linarith)

end EinsteinRelation.Correctors
