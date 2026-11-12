import EinsteinRelation.Correctors.CanonicalScalarTranslation
import EinsteinRelation.Correctors.AKMPlanarSourceShiftedMeans
import EinsteinRelation.Correctors.CanonicalConditionalScalarCorrection

/-! # Planar cancellation for the literal scalar correction

Source: `paper/main.tex:948–963`. The shifted mean is bounded by the
existing AKM input. Normalization gives the translation identity, and the
conditional scalar tail cancels the common term under the derivative weight.
-/

open MeasureTheory
open EinsteinRelation.Carriers (reducedCoefficientObservationSigma)

namespace EinsteinRelation.Correctors
open External.AKM HeatSelectedSkewMeaning
open NormalizedSpatialRepresentativeSupport NormalizedScalarPhysicalLawTransportSupport

local instance : Fact (2 ≤ 2) := ⟨le_rfl⟩

/-- A measurable scalar with a finite conditional-tail moment is integrable;
no separate integrability premise is needed in the cancellation consumer.
Source: `paper/main.tex:956–963`. -/
theorem integrable_of_conditional_tail_bound {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (m : MeasurableSpace Ω)
    {f : Ω → ℝ} (hf : @AEStronglyMeasurable Ω ℝ _ mΩ mΩ f μ)
    {p A : ℝ} (hp : 1 ≤ p)
    (ht : eLpNorm (f - μ[f | m]) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal A) :
    Integrable f μ := by
  letI : MeasurableSpace Ω := mΩ
  by_contra hfi
  rw [condExp_of_not_integrable hfi, sub_zero] at ht
  exact hfi ((show MemLp f (ENNReal.ofReal p) μ from
    ⟨hf, ht.trans_lt ENNReal.ofReal_lt_top⟩).integrable
      (ENNReal.one_le_ofReal.mpr hp))

/-- The actual planar scalar correction has the sharp inverse-radius bound
from the scalar conditional tail and the existing shifted-mean literature
estimate. Continuity is an internal source-selection obligation.
Source: `paper/main.tex:948–963`. -/
theorem canonicalConditionalMollifierFields_planar_scalarCorrection_of_literature
    (hAKM : CorrectorWeakH2) (hP : External.GilbargTrudinger.BallPoincareEstimate)
    (L r₀ p A : ℝ) (hL : 1 ≤ L) (hr₀ : 1 ≤ r₀) (hp : 1 ≤ p) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : EnvironmentLaw 2 L r₀) (R : ℝ) (hR : 1 ≤ R)
      (i : Fin 2) (u : FieldPair 2 → Vec 2 → ℝ) (S : FieldPair 2 → Vec 2 → Mat 2),
      IsNormalizedCanonicalScalarCorrector Q i (canonicalSourceMollifier 2) R hR 0
        (fun ω x => u ω x.ofLp) →
      HasHeatSelectedSkewCorrectorColumn (by omega) Q i S →
      (∀ᵐ ω ∂reducedEnvironmentLaw Q, Continuous (u ω)) →
      eLpNorm ((fun ω => u ω 0) - (reducedEnvironmentLaw Q)[fun ω => u ω 0 |
        reducedCoefficientObservationSigma
          {z : Vec 2 | euclideanNorm (z - 0) < 8 * R}])
        (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal A →
      MemLp (fun ω => euclideanNorm
        ((canonicalConditionalMollifierFields Q i R u S).scalarCorrection ω))
        (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ∧
      eLpNorm (fun ω => euclideanNorm
        ((canonicalConditionalMollifierFields Q i R u S).scalarCorrection ω))
        (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal (C * R⁻¹) := by
  obtain ⟨B, hB, hshift⟩ := canonical_planar_source_shifted_means_of_literature
    hAKM hP L r₀ p hL hr₀ hp
  obtain ⟨W, hW, hbound⟩ := canonicalConditionalMollifierFields_scalarCorrection_bound 2
  refine ⟨(2 * (2 * A + B) * W), by positivity, ?_⟩
  intro Q R hR i u S hu hS huc htail
  have hum : StronglyMeasurable (Function.uncurry u) := by
    simpa only [Function.uncurry, WithLp.ofLp_toLp] using
      (hu.1.comp measurable_swap).stronglyMeasurable
  have huvalue (x : Vec 2) : Measurable (fun ω => u ω x) := by
    simpa only [WithLp.ofLp_toLp] using hu.1.comp (measurable_const.prodMk measurable_id)
  have hf := integrable_of_conditional_tail_bound _ (huvalue 0).aestronglyMeasurable hp htail
  let g : Vec 2 → FieldPair 2 → ℝ := fun y ω => ∫ z,
    (Calculus.unitMassScaledMollifier 2 R z -
      Calculus.unitMassScaledMollifier 2 R (z - y)) * u ω z
  have hg (y : Vec 2) (hy : euclideanNorm y ≤ R) :
      MemLp (g y) (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ∧
        eLpNorm (g y) (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal B := by
    simpa only [g, WithLp.ofLp_toLp] using
      (hshift Q i (canonicalSourceMollifier 2) R hR 0
        (fun ω x => u ω x.ofLp) S hu hS R hR y hy).1
  have hsource (y : Vec 2) := ae_normalizedCanonicalScalar_translation Q i hR u hu huc y
  have hui (y : {y : Vec 2 // euclideanNorm y ≤ R}) :
      Integrable (fun ω => u ω (-y.1)) (reducedEnvironmentLaw Q) := by
    have hpres : MeasurePreserving (translate y.1)
        (reducedEnvironmentLaw Q) (reducedEnvironmentLaw Q) :=
      ⟨Probability.measurable_translate _, reducedEnvironmentLaw_stationary Q _⟩
    apply (hpres.integrable_comp (huvalue (-y.1)).aestronglyMeasurable).mp
    exact (hf.add ((hg y.1 y.2).1.integrable (ENNReal.one_le_ofReal.mpr hp))).congr
      (hsource y.1).symm
  simpa only [Nat.cast_ofNat] using hbound Q i hR u S hum hui (fun ω => u ω 0) hf
    (fun y => g y.1) (fun y => (hg y.1 y.2).1.integrable (ENNReal.one_le_ofReal.mpr hp))
    (fun y => hsource y.1) p A B hp hA hB.le (fun y => (hg y.1 y.2).2) htail

end EinsteinRelation.Correctors
