import EinsteinRelation.Correctors.CorrectorMollifierSourceMomentsFromLiterature
import EinsteinRelation.Correctors.NormalizedSourceDominatedPowerMoment

/-! # Quantitative actual source moments on ordinary balls

Source: `paper/main.tex:715–722,921–925,942–947`. Normalization against the
mollifier controls additive constants, so Lemma 5.1 also bounds the actual
sources under normalized ordinary volume on the ball of radius twice R.
-/

open MeasureTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger HeatSelectedSkewMeaning
open NormalizedSpatialRepresentativeSupport NormalizedScalarPhysicalLawTransportSupport

/-- Probability measure for the spatial averages in Lemma 5.1.
Source: `paper/main.tex:715–722`. -/
noncomputable def correctorBallMeasure (d : ℕ) (R : ℝ) : Measure (Vec d) :=
  (volume (ball (0 : Vec d) (2 * R)))⁻¹ • volume.restrict (ball (0 : Vec d) (2 * R))

/-- Positive-radius corrector ball averages are probability measures.
Source: `paper/main.tex:715–722`. -/
theorem isProbabilityMeasure_correctorBallMeasure {d : ℕ} {R : ℝ} (hR : 0 < R) :
    IsProbabilityMeasure (correctorBallMeasure d R) := by
  let β := volume.restrict (ball (0 : Vec d) (2 * R))
  have hvol := ENNReal.toReal_pos_iff.mp
    (paired_ball_volume_pos_finite (d := d) (show 0 < 2 * R by positivity))
  letI : IsFiniteMeasure β := isFiniteMeasure_restrict.mpr hvol.2.ne
  letI : NeZero β := ⟨by
    intro h
    have hh : β Set.univ = 0 := by rw [h]; simp
    exact hvol.1.ne' (by simpa only [β, Measure.restrict_apply_univ] using hh)⟩
  simpa only [correctorBallMeasure, β, Measure.restrict_apply_univ] using
    (inferInstance : IsProbabilityMeasure ((β Set.univ)⁻¹ • β))

/-- Reflection preserves the normalized centered ball measure.
Source: `paper/main.tex:715–722,942–947`. -/
theorem measurePreserving_neg_correctorBallMeasure (d : ℕ) (R : ℝ) :
    MeasurePreserving (fun x : Vec d => -x) (correctorBallMeasure d R)
      (correctorBallMeasure d R) := by
  let B := ball (0 : Vec d) (2 * R)
  have hpre : (fun x : Vec d => -x) ⁻¹' B = B := by
    ext x
    simp only [B, ball, Set.mem_preimage, Set.mem_setOf_eq, sub_zero, Entropy.euclideanNorm_neg']
  have hneg := (Measure.measurePreserving_neg (volume : Measure (Vec d))).restrict_preimage_emb
    (MeasurableEquiv.neg (Vec d)).measurableEmbedding B
  rw [hpre] at hneg
  refine ⟨measurable_neg, ?_⟩
  change Measure.map _ ((volume B)⁻¹ • volume.restrict B) = _
  rw [Measure.map_smul, hneg.map_eq]
  rfl

/-- Actual scalar and skew-entry norms on ordinary normalized ball volume
follow from the existing eleven literature inputs and the source normalization.
Source: `paper/main.tex:715–722,921–925,942–947`. -/
theorem corrector_ball_source_moments_of_literature
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
          (ENNReal.ofReal p) ((reducedEnvironmentLaw Q).prod (correctorBallMeasure d R)) ∧
        eLpNorm (fun z : FieldPair d × Vec d => u z.1 (-z.2))
          (ENNReal.ofReal p) ((reducedEnvironmentLaw Q).prod (correctorBallMeasure d R)) ≤
          ENNReal.ofReal (C * correctorAmplitude d R)) ∧
      ∀ j k,
        MemLp (fun z : FieldPair d × Vec d => S z.1 (-z.2) j k)
          (ENNReal.ofReal p) ((reducedEnvironmentLaw Q).prod (correctorBallMeasure d R)) ∧
        eLpNorm (fun z : FieldPair d × Vec d => S z.1 (-z.2) j k)
          (ENNReal.ofReal p) ((reducedEnvironmentLaw Q).prod (correctorBallMeasure d R)) ≤
          ENNReal.ofReal (C * correctorAmplitude d R) := by
  obtain ⟨A, hA⟩ := correctorMoments_of_literature
    h45 h46 h47 h68 h614 h615 h616 hP h817 h832 h836 d L r₀ p hp
  obtain ⟨D, hD, hdom⟩ := exists_mollifierCenterMeasure_le_ball_average d
  let B : ℝ := |A| + 1
  have hB : 0 < B := by dsimp only [B]; positivity
  have hp1 : 1 ≤ p := one_le_two.trans hp
  have hp0 : 0 < p := zero_lt_one.trans_le hp1
  let K := 1 + D ^ (1 / p)
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K * B ^ (1 / p), by positivity, ?_⟩
  intro Q R hR i u S hu hS hSm hSzero
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  letI := isProbabilityMeasure_correctorBallMeasure (d := d) hR0
  letI := isProbabilityMeasure_mollifierCenterMeasure (d := d) hR0
  have hum : StronglyMeasurable (Function.uncurry u) := by
    simpa only [Function.uncurry, WithLp.ofLp_toLp] using
      (hu.1.comp measurable_swap).stronglyMeasurable
  have hmneg : Measurable (fun z : FieldPair d × Vec d => (z.1, -z.2)) :=
    measurable_fst.prodMk measurable_snd.neg
  have hcm (w : FieldPair d → Vec d → ℝ) (hw : StronglyMeasurable (Function.uncurry w)) :
      StronglyMeasurable (fun ω => ⨍ z in ball (0 : Vec d) (2 * R), w ω z ∂volume) := by
    simp only [average_eq]
    exact (hw.integral_prod_right'
      (ν := volume.restrict (ball (0 : Vec d) (2 * R)))).const_smul
        (((volume.restrict (ball (0 : Vec d) (2 * R))).real Set.univ)⁻¹ : ℝ)
  have ha : 0 ≤ correctorAmplitude d R := by
    unfold correctorAmplitude; split <;> positivity
  have hscale : K * (max (B * correctorAmplitude d R ^ p) 0) ^ (1 / p) =
      (K * B ^ (1 / p)) * correctorAmplitude d R := by
    rw [max_eq_left (mul_nonneg hB.le (Real.rpow_nonneg ha p)),
      Real.mul_rpow hB.le (Real.rpow_nonneg ha p), ← Real.rpow_mul ha,
      mul_one_div_cancel hp0.ne', Real.rpow_one]
    ring
  have hpair := (hA Q (canonicalSourceMollifier d)).2 R hR 0 i
    (fun ω x => u ω x.ofLp) S hu hS
  simp only [centered_scalar_flux_average_toLp, WithLp.ofLp_zero] at hpair
  have hpair' := hpair.trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (show A ≤ B by dsimp only [B]; linarith [le_abs_self A])
      (Real.rpow_nonneg ha p)))
  have htransfer (w : FieldPair d → Vec d → ℝ)
      (hw : StronglyMeasurable (Function.uncurry w))
      (hz : ∀ᵐ ω ∂reducedEnvironmentLaw Q,
        (∫ y, w ω (-y) ∂mollifierCenterMeasure d R) = 0)
      (hb : (∫⁻ ω, ⨍⁻ x in ball (0 : Vec d) (2 * R),
        ENNReal.ofReal (|w ω x - ⨍ z in ball (0 : Vec d) (2 * R), w ω z ∂volume| ^ p)
          ∂volume ∂reducedEnvironmentLaw Q) ≤ ENNReal.ofReal (B * correctorAmplitude d R ^ p)) :
      MemLp (fun z : FieldPair d × Vec d => w z.1 (-z.2)) (ENNReal.ofReal p)
          ((reducedEnvironmentLaw Q).prod (correctorBallMeasure d R)) ∧
        eLpNorm (fun z : FieldPair d × Vec d => w z.1 (-z.2)) (ENNReal.ofReal p)
          ((reducedEnvironmentLaw Q).prod (correctorBallMeasure d R)) ≤
          ENNReal.ofReal ((K * B ^ (1 / p)) * correctorAmplitude d R) := by
    have hbneg : (∫⁻ ω, ∫⁻ y,
        ENNReal.ofReal (|w ω (-y) - ⨍ z in ball (0 : Vec d) (2 * R), w ω z ∂volume| ^ p)
          ∂correctorBallMeasure d R ∂reducedEnvironmentLaw Q) ≤
          ENNReal.ofReal (B * correctorAmplitude d R ^ p) := by
      have heq (ω : FieldPair d) :=
        (measurePreserving_neg_correctorBallMeasure d R).lintegral_comp_emb
          (MeasurableEquiv.neg (Vec d)).measurableEmbedding
          (fun x => ENNReal.ofReal
            (|w ω x - ⨍ z in ball (0 : Vec d) (2 * R), w ω z ∂volume| ^ p))
      simp_rw [heq]
      simpa only [correctorBallMeasure, lintegral_smul_measure, smul_eq_mul,
        laverage_eq, Measure.restrict_apply_univ, div_eq_mul_inv, mul_comm] using hb
    obtain ⟨hm, hn⟩ := memLp_normalized_source_of_dominated_centered_power_moment
      (reducedEnvironmentLaw Q) (mollifierCenterMeasure d R) (correctorBallMeasure d R)
      hp1 hD.le (hdom R hR0) (fun ω y => w ω (-y)) (hw.comp_measurable hmneg)
      _ (hcm w hw) hz hbneg
    exact ⟨hm, by simpa only [← hscale, K] using hn⟩
  constructor
  · apply htransfer u hum (normalizedCanonicalScalar_mollifierCenterMean_eq_zero Q i hR u hu)
    simp only [laverage_eq] at hpair' ⊢
    exact (lintegral_mono fun _ => ENNReal.div_le_div_right
      (lintegral_mono fun _ => le_add_right le_rfl) _).trans hpair'
  · intro j k
    apply htransfer (fun ω x => S ω x j k) (hSm j k) (hSzero j k)
    simp only [laverage_eq] at hpair' ⊢
    refine (lintegral_mono fun ω => ENNReal.div_le_div_right
      (lintegral_mono fun x => ?_) _).trans hpair'
    apply (le_add_left le_rfl).trans'
    apply ENNReal.ofReal_le_ofReal
    exact Real.rpow_le_rpow (abs_nonneg _)
      (abs_entry_le_frobeniusNorm (S ω x - Matrix.of (fun a b =>
        ⨍ z in ball (0 : Vec d) (2 * R), S ω z a b ∂volume)) j k) hp0.le

end EinsteinRelation.Correctors
