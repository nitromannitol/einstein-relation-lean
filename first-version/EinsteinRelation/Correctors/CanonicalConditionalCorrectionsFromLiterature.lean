import EinsteinRelation.Correctors.CanonicalConditionalCorrectionsFromSpatialMoments

/-! # Literal common-field corrections from the existing literature inputs

Source: `paper/main.tex:715–722,942–947`. Lemma 5.1 supplies the actual
joint source moments used by both derivative corrections. This gives the
sharp inverse-radius rate in dimension at least three. The planar
logarithmic amplitude needs the separate conditional-tail cancellation.
-/

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger HeatSelectedSkewMeaning
open NormalizedSpatialRepresentativeSupport NormalizedScalarPhysicalLawTransportSupport

/-- Both actual Euclidean derivative corrections are bounded by the
corrector amplitude divided by R, using only the existing eleven literature
inputs and the actual normalized source pair.
Source: `paper/main.tex:715–722,942–947`. -/
theorem canonicalConditionalMollifierFields_corrections_of_literature
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
      (MemLp (fun ω => euclideanNorm
          ((canonicalConditionalMollifierFields Q i R u S).scalarCorrection ω))
          (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ∧
        eLpNorm (fun ω => euclideanNorm
          ((canonicalConditionalMollifierFields Q i R u S).scalarCorrection ω))
          (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤
          ENNReal.ofReal (C * correctorAmplitude d R * R⁻¹)) ∧
      (MemLp (fun ω => euclideanNorm
          ((canonicalConditionalMollifierFields Q i R u S).skewCorrection ω))
          (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ∧
        eLpNorm (fun ω => euclideanNorm
          ((canonicalConditionalMollifierFields Q i R u S).skewCorrection ω))
          (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤
          ENNReal.ofReal (C * correctorAmplitude d R * R⁻¹)) := by
  obtain ⟨A, hA, hsource⟩ := corrector_ball_source_moments_of_literature
    h45 h46 h47 h68 h614 h615 h616 hP h817 h832 h836 d L r₀ p hp
  obtain ⟨W, hW, hscalar⟩ :=
    canonicalConditionalMollifierFields_scalarCorrection_of_spatial_moments d
  obtain ⟨V, hV, hskew⟩ :=
    canonicalConditionalMollifierFields_skewCorrection_of_spatial_moments d
  refine ⟨(W + V) * A, by positivity, ?_⟩
  intro Q R hR i u S hu hS hSm hSzero
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hp1 : 1 ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr (one_le_two.trans hp)
  have ha : 0 ≤ correctorAmplitude d R := by
    unfold correctorAmplitude; split <;> positivity
  have hum : StronglyMeasurable (Function.uncurry u) := by
    simpa only [Function.uncurry, WithLp.ofLp_toLp] using
      (hu.1.comp measurable_swap).stronglyMeasurable
  obtain ⟨huM, hSM⟩ := hsource Q R hR i u S hu hS hSm hSzero
  have hH := hscalar Q i hR0 hp1 ENNReal.ofReal_ne_top (mul_nonneg hA.le ha)
    u S hum hSm huM.1 huM.2
  have hK := hskew Q i hR0 hp1 ENNReal.ofReal_ne_top (mul_nonneg hA.le ha)
    u S hum hSm (fun j k => (hSM j k).1) (fun j k => (hSM j k).2)
  have hle (a b : ℝ) (hb : 0 ≤ b) :
      a * (A * correctorAmplitude d R) * R⁻¹ ≤
        ((a + b) * A) * correctorAmplitude d R * R⁻¹ := by
    have ht : 0 ≤ b * (A * correctorAmplitude d R) * R⁻¹ := by positivity
    nlinarith only [ht]
  exact ⟨⟨hH.1, hH.2.trans (ENNReal.ofReal_le_ofReal (hle W V hV.le))⟩,
    ⟨hK.1, hK.2.trans (ENNReal.ofReal_le_ofReal (by
      simpa only [add_comm V W] using hle V W hW.le))⟩⟩

/-- In dimension at least three the actual corrections have a uniform
inverse-radius bound, with no conditional-tail premise.
Source: `paper/main.tex:942–947`. -/
theorem canonicalConditionalMollifierFields_corrections_of_literature_of_three_le
    (h45 : ScalarStationaryEstimate) (h46 : ScalarPlanarL2Estimate)
    (h47 : ScalarHeatDifferenceEstimate) (h68 : FluxGradientEstimate)
    (h614 : FluxStationaryEstimate) (h615 : FluxPlanarL2Estimate)
    (h616 : FluxHeatDifferenceEstimate) (hP : BallPoincareEstimate)
    (h817 : LocalBoundednessEstimate) (h832 : InteriorGradientEstimate)
    (h836 : InteriorRegularRepresentative)
    (d : ℕ) [Fact (2 ≤ d)] (L r₀ p : ℝ) (hp : 2 ≤ p) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : EnvironmentLaw d L r₀)
      (R : ℝ) (hR : 1 ≤ R) (i : Fin d)
      (u : FieldPair d → Vec d → ℝ) (S : FieldPair d → Vec d → Mat d),
      IsNormalizedCanonicalScalarCorrector Q i (canonicalSourceMollifier d) R hR 0
        (fun ω x => u ω x.ofLp) →
      HasHeatSelectedSkewCorrectorColumn (Fact.out : 2 ≤ d) Q i S →
      (∀ j k, StronglyMeasurable (fun z : FieldPair d × Vec d => S z.1 z.2 j k)) →
      (∀ j k, ∀ᵐ ω ∂reducedEnvironmentLaw Q,
        (∫ y, S ω (-y) j k ∂mollifierCenterMeasure d R) = 0) →
      (MemLp (fun ω => euclideanNorm
          ((canonicalConditionalMollifierFields Q i R u S).scalarCorrection ω))
          (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ∧
        eLpNorm (fun ω => euclideanNorm
          ((canonicalConditionalMollifierFields Q i R u S).scalarCorrection ω))
          (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤
          ENNReal.ofReal (C * R⁻¹)) ∧
      (MemLp (fun ω => euclideanNorm
          ((canonicalConditionalMollifierFields Q i R u S).skewCorrection ω))
          (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ∧
        eLpNorm (fun ω => euclideanNorm
          ((canonicalConditionalMollifierFields Q i R u S).skewCorrection ω))
          (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤
          ENNReal.ofReal (C * R⁻¹)) := by
  obtain ⟨C, hC, hbound⟩ := canonicalConditionalMollifierFields_corrections_of_literature
    h45 h46 h47 h68 h614 h615 h616 hP h817 h832 h836 d L r₀ p hp
  refine ⟨C, hC, ?_⟩
  intro Q R hR i u S hu hS hSm hSzero
  have h := hbound Q R hR i u S hu hS hSm hSzero
  simpa only [correctorAmplitude, if_pos hd, mul_one] using h

end EinsteinRelation.Correctors
