import EinsteinRelation.Correctors.CorrectorMollifierSourceMomentsFromLiterature
import EinsteinRelation.Correctors.CanonicalConditionalSpatialAmplitude

/-! # Literature instantiation of the common conditional amplitude

Source: `paper/main.tex:942–947`. Lemma 5.1 controls the very scalar and
skew sources used by the common conditional mollifier fields. Only the
source existence and its skew additive normalization remain internal.
-/

open MeasureTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger HeatSelectedSkewMeaning
open NormalizedSpatialRepresentativeSupport NormalizedScalarPhysicalLawTransportSupport

/-- The common conditional scalar and Frobenius skew amplitudes have the
paper's uniform corrector scale, from existing frozen literature inputs.
Source: `paper/main.tex:942–947`. -/
theorem canonicalConditionalMollifierFields_amplitude_of_literature
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
      let f := canonicalConditionalMollifierFields Q i R u S
      eLpNorm f.scalar (ENNReal.ofReal p) (reducedEnvironmentLaw Q) +
        eLpNorm (fun ω => frobeniusNorm (f.skew ω))
          (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤
          ENNReal.ofReal (C * correctorAmplitude d R) := by
  obtain ⟨A, hA, hb⟩ := corrector_mollifier_source_moments_of_literature
    h45 h46 h47 h68 h614 h615 h616 hP h817 h832 h836 d L r₀ p hp
  refine ⟨(1 + (d : ℝ) * d) * A, by positivity, ?_⟩
  intro Q R hR i u S hu hS hSm hSzero
  obtain ⟨⟨humem, hub⟩, hSb⟩ := hb Q R hR i u S hu hS hSm hSzero
  have hum : StronglyMeasurable (Function.uncurry u) := by
    simpa only [Function.uncurry, WithLp.ofLp_toLp] using
      (hu.1.comp measurable_swap).stronglyMeasurable
  have ha : 0 ≤ correctorAmplitude d R := by
    unfold correctorAmplitude; split <;> positivity
  have ht := canonicalConditionalMollifierFields_amplitude_bound_of_spatial_moments
    Q i (zero_lt_one.trans_le hR) (one_le_two.trans hp) (mul_nonneg hA.le ha)
    u S hum hSm humem (fun j k => (hSb j k).1) hub (fun j k => (hSb j k).2)
  simpa only [mul_assoc] using ht

end EinsteinRelation.Correctors
