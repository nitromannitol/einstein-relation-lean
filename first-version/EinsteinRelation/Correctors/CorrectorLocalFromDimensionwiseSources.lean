import EinsteinRelation.Correctors.DimensionwiseLocalCorrectorAssembly
import EinsteinRelation.Correctors.CanonicalConditionalSpatialEquationsFromLiterature
import EinsteinRelation.Correctors.CanonicalConditionalAmplitudeFromLiterature
import EinsteinRelation.Correctors.CanonicalConditionalGradientEstimate
import EinsteinRelation.Correctors.CanonicalConditionalCorrectionsFromLiterature
import EinsteinRelation.Correctors.CanonicalPlanarSkewCorrection
import EinsteinRelation.Mobility.CorrectorLocalFromConstruction

/-! # Proposition 5.3 assembly for the actual canonical source fields

Source: `paper/main.tex:895–977`. The source fields are fixed before the
moment exponent. Literature estimates give their amplitude and spatial
equations, and conditional source tails give the remaining sharp errors.
The source construction and conditional-tail estimates are internal
obligations; this module does not assume a local-corrector conclusion.
-/

open MeasureTheory
open EinsteinRelation.Carriers (reducedCoefficientObservationSigma)

namespace EinsteinRelation
open Correctors External.AKM External.GilbargTrudinger HeatSelectedSkewMeaning
open Correctors.NormalizedSpatialRepresentativeSupport
open Correctors.StationarySpatialRealization (spatialRealization)
open Correctors.NormalizedScalarPhysicalLawTransportSupport

local instance : Fact (2 ≤ (2 : ℕ)) := ⟨le_rfl⟩

section CanonicalSources

variable
    (u : ∀ {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ}, EnvironmentLaw d L r₀ → ℝ → Fin d →
      FieldPair d → Vec d → ℝ)
    (S : ∀ {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ}, EnvironmentLaw d L r₀ → ℝ → Fin d →
      FieldPair d → Vec d → Mat d)
    (hu : ∀ {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ}
      (Q : EnvironmentLaw d L r₀) (R : ℝ) (hR : 1 ≤ R) (i : Fin d),
      IsNormalizedCanonicalScalarCorrector Q i (canonicalSourceMollifier d) R hR 0
        (fun ω x => u Q R i ω x.ofLp))
    (hS : ∀ {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ}
      (Q : EnvironmentLaw d L r₀) (R : ℝ), 1 ≤ R → ∀ i : Fin d,
      HasHeatSelectedSkewCorrectorColumn (Fact.out : 2 ≤ d) Q i (S Q R i))
    (hSm : ∀ {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ}
      (Q : EnvironmentLaw d L r₀) (R : ℝ), 1 ≤ R → ∀ i j k : Fin d,
      StronglyMeasurable (fun z : FieldPair d × Vec d => S Q R i z.1 z.2 j k))
    (hSsk : ∀ {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ}
      (Q : EnvironmentLaw d L r₀) (R : ℝ), 1 ≤ R → ∀ (i : Fin d) (ω : FieldPair d)
        (x : Vec d), (S Q R i ω x).transpose = -(S Q R i ω x))
    (hSn : ∀ {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ}
      (Q : EnvironmentLaw d L r₀) (R : ℝ), 1 ≤ R → ∀ i j k : Fin d,
      ∀ᵐ ω ∂reducedEnvironmentLaw Q,
        (∫ z, S Q R i ω (-z) j k ∂mollifierCenterMeasure d R) = 0)
    (huc : ∀ {L r₀ : ℝ} (Q : EnvironmentLaw 2 L r₀) (R : ℝ),
      1 ≤ R → ∀ i : Fin 2, ∀ᵐ ω ∂reducedEnvironmentLaw Q, Continuous (u Q R i ω))
    (hSc : ∀ {L r₀ : ℝ} (Q : EnvironmentLaw 2 L r₀) (R : ℝ),
      1 ≤ R → ∀ i : Fin 2, ∀ᵐ ω ∂reducedEnvironmentLaw Q, Continuous (S Q R i ω))
    (hgradientTail : ∀ (d : ℕ) [Fact (2 ≤ d)] (L r₀ p : ℝ), 2 ≤ p →
      ∃ A : ℝ, 0 ≤ A ∧ ∀ (Q : EnvironmentLaw d L r₀) (R : ℝ), 1 ≤ R → ∀ i : Fin d,
        eLpNorm (fun ω => euclideanNorm
          (((canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2
            (reducedEnvironmentLaw Q)) ω).ofLp -
            (reducedEnvironmentLaw Q)[fun a =>
              ((canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2
                (reducedEnvironmentLaw Q)) a).ofLp |
              reducedCoefficientObservationSigma
                {z : Vec d | euclideanNorm (z - 0) < 8 * R}] ω))
          (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤
            ENNReal.ofReal (A * R ^ (-(d : ℝ) / 2)))
    (hplanarTail : ∀ L r₀ p : ℝ, 2 ≤ p → ∃ A : ℝ, 0 ≤ A ∧
      ∀ (Q : EnvironmentLaw 2 L r₀) (R : ℝ), 1 ≤ R → ∀ i : Fin 2,
        (eLpNorm ((fun ω => u Q R i ω 0) - (reducedEnvironmentLaw Q)[
          fun ω => u Q R i ω 0 | reducedCoefficientObservationSigma
            {z : Vec 2 | euclideanNorm (z - 0) < 8 * R}])
          (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal A) ∧
        (eLpNorm (fun ω => frobeniusNorm (fun j k => S Q R i ω 0 j k -
          (reducedEnvironmentLaw Q)[fun a => S Q R i a 0 j k |
            reducedCoefficientObservationSigma
              {z : Vec 2 | euclideanNorm (z - 0) < 8 * R}] ω))
          (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal A))

include hu hS hSm hSn huc hSc hplanarTail

/-- Uniform sharp bounds for both literal corrections, including the
planar conditional cancellation. The source pair is fixed before p.
Source: `paper/main.tex:942–963`. -/
theorem canonicalConditionalMollifierFields_dimensionwise_corrections_of_source_tails
    (h45 : ScalarStationaryEstimate) (h46 : ScalarPlanarL2Estimate)
    (h47 : ScalarHeatDifferenceEstimate) (h68 : FluxGradientEstimate)
    (h614 : FluxStationaryEstimate) (h615 : FluxPlanarL2Estimate)
    (h616 : FluxHeatDifferenceEstimate) (hP : BallPoincareEstimate)
    (h817 : LocalBoundednessEstimate) (h832 : InteriorGradientEstimate)
    (h836 : InteriorRegularRepresentative) (hH2 : CorrectorWeakH2)
    (d : ℕ) [Fact (2 ≤ d)] (L r₀ p : ℝ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q : EnvironmentLaw d L r₀) (R : ℝ), 1 ≤ R → ∀ i : Fin d,
      let f := canonicalConditionalMollifierFields Q i R (u Q R i) (S Q R i)
      eLpNorm (fun ω => euclideanNorm (f.scalarCorrection ω))
        (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal (C * R⁻¹) ∧
      eLpNorm (fun ω => euclideanNorm (f.skewCorrection ω))
        (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal (C * R⁻¹) := by
  by_cases hd : 3 ≤ d
  · obtain ⟨C, hC, hb⟩ :=
      canonicalConditionalMollifierFields_corrections_of_literature_of_three_le
        h45 h46 h47 h68 h614 h615 h616 hP h817 h832 h836 d L r₀ p hp hd
    refine ⟨C, hC.le, ?_⟩
    intro Q R hR i
    have h := hb Q R hR i (u Q R i) (S Q R i) (hu Q R hR i)
      (hS Q R hR i) (hSm Q R hR i) (hSn Q R hR i)
    exact ⟨h.1.2, h.2.2⟩
  · have hd2 : d = 2 := by have := (Fact.out : 2 ≤ d); omega
    subst d
    by_cases hL : 1 ≤ L
    · by_cases hr₀ : 1 ≤ r₀
      · obtain ⟨A, hA, htail⟩ := hplanarTail L r₀ p hp
        obtain ⟨C, hC, hc⟩ :=
          canonicalConditionalMollifierFields_planar_scalarCorrection_of_literature
            hH2 hP L r₀ p A hL hr₀ (one_le_two.trans hp) hA
        obtain ⟨D, hD, hd⟩ :=
          canonicalConditionalMollifierFields_planar_skewCorrection_of_literature
            hH2 hP L r₀ p A hL hr₀ (one_le_two.trans hp) hA
        refine ⟨C + D, by positivity, ?_⟩
        intro Q R hR i
        have ht := htail Q R hR i
        have hs := hc Q R hR i (u Q R i) (S Q R i) (hu Q R hR i)
          (hS Q R hR i) (huc Q R hR i) ht.1
        have hk := hd Q R hR i (u Q R i) (S Q R i) (hu Q R hR i)
          (hS Q R hR i) (hSm Q R hR i) (hSc Q R hR i) (hSn Q R hR i) ht.2
        exact ⟨hs.2.trans (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hD.le) (by positivity))),
          hk.2.trans (ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC.le) (by positivity)))⟩
      · refine ⟨0, le_rfl, ?_⟩
        intro Q R hR i
        exact (hr₀ Q.range_parameter).elim
    · refine ⟨0, le_rfl, ?_⟩
      intro Q R hR i
      exact (hL Q.ellipticity_parameter).elim

include hSsk hgradientTail

/-- The actual normalized scalar and heat-selected skew sources, the existing
literature estimates and the indicated conditional source tails imply the
production Proposition 5.3 construction. Source existence and tail estimates
remain explicit internal obligations. Source: `paper/main.tex:895–977`. -/
theorem correctorLocalConstruction_of_dimensionwise_sources_and_tails
    (h45 : ScalarStationaryEstimate) (h46 : ScalarPlanarL2Estimate)
    (h47 : ScalarHeatDifferenceEstimate) (h68 : FluxGradientEstimate)
    (h614 : FluxStationaryEstimate) (h615 : FluxPlanarL2Estimate)
    (h616 : FluxHeatDifferenceEstimate) (hP : BallPoincareEstimate)
    (h817 : LocalBoundednessEstimate) (h832 : InteriorGradientEstimate)
    (h836 : InteriorRegularRepresentative) (hH2 : CorrectorWeakH2) :
    CorrectorLocalConstruction := by
  let fields : ∀ {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ}, EnvironmentLaw d L r₀ → ℝ → Fin d →
      LocalCorrectorFields d := fun Q R i =>
    canonicalConditionalMollifierFields Q i R (u Q R i) (S Q R i)
  have hcorrections (d : ℕ) [Fact (2 ≤ d)] (L r₀ p : ℝ) (hp : 2 ≤ p) := by
    exact canonicalConditionalMollifierFields_dimensionwise_corrections_of_source_tails
      u S hu hS hSm hSn huc hSc hplanarTail
      h45 h46 h47 h68 h614 h615 h616 hP h817 h832 h836 hH2 d L r₀ p hp
  apply correctorLocalConstruction_of_dimensionwise_spatial_fields fields
  · intro d _ L r₀ Q R hR i
    have hum : StronglyMeasurable (Function.uncurry (u Q R i)) := by
      simpa only [Function.uncurry, WithLp.ofLp_toLp] using
        ((hu Q R hR i).1.comp measurable_swap).stronglyMeasurable
    simpa only [sub_zero] using measurable_canonicalConditionalMollifierFields Q i
      (zero_lt_one.trans_le hR) (u Q R i) (S Q R i) hum (hSm Q R hR i)
  · intro d _ L r₀ Q R hR i ω
    exact canonicalConditionalMollifierFields_skew Q i R (u Q R i) (S Q R i)
      (hSsk Q R hR i) ω
  · intro d _ L r₀ Q R hR i
    exact ae_canonicalConditionalMollifierFields_spatial_equations_of_literature
      h45 h46 h47 h68 h614 h615 h616 hP h817 h832 h836 Q hR i
      (u Q R i) (S Q R i) (hu Q R hR i) (hS Q R hR i)
      (hSm Q R hR i) (hSn Q R hR i)
  · intro d _ L r₀ p hp
    obtain ⟨C, _, hb⟩ := canonicalConditionalMollifierFields_amplitude_of_literature
      h45 h46 h47 h68 h614 h615 h616 hP h817 h832 h836 d L r₀ p hp
    exact ⟨C, fun Q R hR i => hb Q R hR i (u Q R i) (S Q R i)
      (hu Q R hR i) (hS Q R hR i) (hSm Q R hR i) (hSn Q R hR i)⟩
  · intro d _ L r₀ p hp
    obtain ⟨A, hA, ht⟩ := hgradientTail d L r₀ p hp
    refine ⟨A, hA, ?_⟩
    intro Q R hR i
    exact (canonicalConditionalMollifierFields_gradient_error Q i hR
      (u Q R i) (S Q R i) (one_le_two.trans hp) (by positivity)
      (ht Q R hR i)).2
  · intro d _ L r₀ p hp
    obtain ⟨C, hC, hb⟩ := hcorrections d L r₀ p hp
    exact ⟨C, hC, fun Q R hR i => (hb Q R hR i).1⟩
  · intro d _ L r₀ p hp
    obtain ⟨C, hC, hb⟩ := hcorrections d L r₀ p hp
    exact ⟨C, hC, fun Q R hR i => (hb Q R hR i).2⟩

end CanonicalSources
end EinsteinRelation
