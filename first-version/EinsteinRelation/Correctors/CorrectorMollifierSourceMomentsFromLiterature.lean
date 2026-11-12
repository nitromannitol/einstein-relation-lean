import EinsteinRelation.Correctors.CorrectorMollifierMomentsFromLiterature
import EinsteinRelation.Correctors.NormalizedSourceMomentBound
import EinsteinRelation.Correctors.NormalizedScalarMollifierMean
import EinsteinRelation.Correctors.CoordinateMomentProjections

/-! # Actual normalized source norms from Lemma 5.1

Source: `paper/main.tex:715–722,913–925,942–947`. The existing literature
inputs give absolute mollifier-weighted scalar and skew-entry source norms.
The scalar mean identity follows from its canonical normalization. The
skew mean identity is an internal choice of additive spatial constants.
-/

open MeasureTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger HeatSelectedSkewMeaning
open NormalizedSpatialRepresentativeSupport NormalizedScalarPhysicalLawTransportSupport

/-- The source moments required by the common conditional fields follow
from the proved Lemma 5.1 once the heat-selected skew source is normalized.
The last hypothesis specifies only its additive spatial constants.
Source: `paper/main.tex:715–722,913–925,942–947`. -/
theorem corrector_mollifier_source_moments_of_literature
    (h45 : ScalarStationaryEstimate) (h46 : ScalarPlanarL2Estimate)
    (h47 : ScalarHeatDifferenceEstimate) (h68 : FluxGradientEstimate)
    (h614 : FluxStationaryEstimate) (h615 : FluxPlanarL2Estimate)
    (h616 : FluxHeatDifferenceEstimate) (hP : BallPoincareEstimate)
    (h817 : LocalBoundednessEstimate) (h832 : InteriorGradientEstimate)
    (h836 : InteriorRegularRepresentative)
    (d : ℕ) [Fact (2 ≤ d)] (L r₀ p : ℝ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : EnvironmentLaw d L r₀)
      (R : ℝ) (hR : 1 ≤ R) (i : Fin d)
      (u : FieldPair d → Vec d → ℝ) (S : FieldPair d → Vec d → Mat d),
      IsNormalizedCanonicalScalarCorrector Q i (canonicalSourceMollifier d) R hR 0
        (fun ω x => u ω x.ofLp) →
      HasHeatSelectedSkewCorrectorColumn (Fact.out : 2 ≤ d) Q i S →
      (∀ j k, StronglyMeasurable (fun z : FieldPair d × Vec d => S z.1 z.2 j k)) →
      (∀ j k, ∀ᵐ ω ∂reducedEnvironmentLaw Q,
        (∫ y, S ω (-y) j k ∂mollifierCenterMeasure d R) = 0) →
      (MemLp (fun z : FieldPair d × Vec d => u z.1 (-z.2))
          (ENNReal.ofReal p) ((reducedEnvironmentLaw Q).prod (mollifierCenterMeasure d R)) ∧
        eLpNorm (fun z : FieldPair d × Vec d => u z.1 (-z.2))
          (ENNReal.ofReal p) ((reducedEnvironmentLaw Q).prod (mollifierCenterMeasure d R)) ≤
          ENNReal.ofReal (C * correctorAmplitude d R)) ∧
      ∀ j k,
        MemLp (fun z : FieldPair d × Vec d => S z.1 (-z.2) j k)
          (ENNReal.ofReal p) ((reducedEnvironmentLaw Q).prod (mollifierCenterMeasure d R)) ∧
        eLpNorm (fun z : FieldPair d × Vec d => S z.1 (-z.2) j k)
          (ENNReal.ofReal p) ((reducedEnvironmentLaw Q).prod (mollifierCenterMeasure d R)) ≤
          ENNReal.ofReal (C * correctorAmplitude d R) := by
  obtain ⟨A, hA, hb⟩ := corrector_mollifier_centered_moments_of_literature
    h45 h46 h47 h68 h614 h615 h616 hP h817 h832 h836 d L r₀ p hp
  have hp1 : 1 ≤ p := one_le_two.trans hp
  have hp0 : 0 < p := zero_lt_one.trans_le hp1
  refine ⟨2 * A ^ (1 / p), by positivity, ?_⟩
  intro Q R hR i u S hu hS hSm hSzero
  letI := isProbabilityMeasure_mollifierCenterMeasure (d := d) (zero_lt_one.trans_le hR)
  have hum : StronglyMeasurable (Function.uncurry u) := by
    simpa only [Function.uncurry, WithLp.ofLp_toLp] using
      (hu.1.comp measurable_swap).stronglyMeasurable
  have hneg : Measurable (fun z : FieldPair d × Vec d => (z.1, -z.2)) :=
    measurable_fst.prodMk measurable_snd.neg
  have hcm : StronglyMeasurable (fun ω =>
      ⨍ z in ball (0 : Vec d) (2 * R), u ω z ∂volume) := by
    simp only [average_eq]
    exact (hum.integral_prod_right' (ν := volume.restrict (ball (0 : Vec d) (2 * R)))).const_smul
      (((volume.restrict (ball (0 : Vec d) (2 * R))).real Set.univ)⁻¹ : ℝ)
  have htm (j k : Fin d) : StronglyMeasurable (fun ω =>
      ⨍ z in ball (0 : Vec d) (2 * R), S ω z j k ∂volume) := by
    simp only [average_eq]
    exact ((hSm j k).integral_prod_right'
      (ν := volume.restrict (ball (0 : Vec d) (2 * R)))).const_smul
      (((volume.restrict (ball (0 : Vec d) (2 * R))).real Set.univ)⁻¹ : ℝ)
  have ha : 0 ≤ correctorAmplitude d R := by
    unfold correctorAmplitude; split <;> positivity
  have hscale : 2 * (max (A * correctorAmplitude d R ^ p) 0) ^ (1 / p) =
      (2 * A ^ (1 / p)) * correctorAmplitude d R := by
    rw [max_eq_left (mul_nonneg hA.le (Real.rpow_nonneg ha p)),
      Real.mul_rpow hA.le (Real.rpow_nonneg ha p), ← Real.rpow_mul ha,
      mul_one_div_cancel hp0.ne', Real.rpow_one]
    ring
  have hpair := hb Q (canonicalSourceMollifier d) R hR i u S hu hS
  constructor
  · have hs : (∫⁻ ω, ∫⁻ y,
        ENNReal.ofReal (|u ω (-y) - ⨍ z in ball (0 : Vec d) (2 * R), u ω z ∂volume| ^ p)
        ∂mollifierCenterMeasure d R ∂reducedEnvironmentLaw Q) ≤
        ENNReal.ofReal (A * correctorAmplitude d R ^ p) :=
      (lintegral_mono fun _ => lintegral_mono fun _ => le_add_right le_rfl).trans hpair
    obtain ⟨hm, hn⟩ := memLp_normalized_source_of_nested_centered_power_moment
      (reducedEnvironmentLaw Q) (mollifierCenterMeasure d R) hp1
      (fun ω y => u ω (-y)) (hum.comp_measurable hneg) _ hcm
      (normalizedCanonicalScalar_mollifierCenterMean_eq_zero Q i hR u hu) hs
    exact ⟨hm, by simpa only [hscale] using hn⟩
  · intro j k
    have hs : (∫⁻ ω, ∫⁻ y,
        ENNReal.ofReal (|S ω (-y) j k -
          ⨍ z in ball (0 : Vec d) (2 * R), S ω z j k ∂volume| ^ p)
        ∂mollifierCenterMeasure d R ∂reducedEnvironmentLaw Q) ≤
        ENNReal.ofReal (A * correctorAmplitude d R ^ p) := by
      refine (lintegral_mono fun ω => lintegral_mono fun y => ?_).trans hpair
      apply (le_add_left le_rfl).trans'
      apply ENNReal.ofReal_le_ofReal
      apply Real.rpow_le_rpow (abs_nonneg _) _ hp0.le
      exact abs_entry_le_frobeniusNorm
        (S ω (-y) - Matrix.of (fun a b =>
          ⨍ z in ball (0 : Vec d) (2 * R), S ω z a b ∂volume)) j k
    obtain ⟨hm, hn⟩ := memLp_normalized_source_of_nested_centered_power_moment
      (reducedEnvironmentLaw Q) (mollifierCenterMeasure d R) hp1
      (fun ω y => S ω (-y) j k) ((hSm j k).comp_measurable hneg) _ (htm j k)
      (hSzero j k) hs
    exact ⟨hm, by simpa only [hscale] using hn⟩

end EinsteinRelation.Correctors
