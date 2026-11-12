import EinsteinRelation.Correctors.CorrectorLocalFromDimensionwiseSources
import EinsteinRelation.Correctors.SelectedCanonicalScalarSource

/-! # Proposition 5.3 with the scalar source constructed

Source: `paper/main.tex:762–766,895–977`. The scalar family is selected
from the proved measurable normalized-potential construction. The skew
source, continuous representatives and conditional tails remain internal
obligations, explicitly supplied below.
-/

open MeasureTheory
open EinsteinRelation.Carriers (reducedCoefficientObservationSigma)
namespace EinsteinRelation
open Correctors External.AKM External.GilbargTrudinger HeatSelectedSkewMeaning
open Correctors.NormalizedSpatialRepresentativeSupport
open Correctors.NormalizedScalarPhysicalLawTransportSupport
local instance : Fact (2 ≤ (2 : ℕ)) := ⟨le_rfl⟩

variable
    (hP : BallPoincareEstimate)
    (S : ∀ {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ}, EnvironmentLaw d L r₀ → ℝ → Fin d →
      FieldPair d → Vec d → Mat d)
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
      1 ≤ R → ∀ i : Fin 2, ∀ᵐ ω ∂reducedEnvironmentLaw Q, Continuous (selectedCanonicalScalarSource hP Q R i ω))
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
        (eLpNorm ((fun ω => selectedCanonicalScalarSource hP Q R i ω 0) - (reducedEnvironmentLaw Q)[
          fun ω => selectedCanonicalScalarSource hP Q R i ω 0 | reducedCoefficientObservationSigma
            {z : Vec 2 | euclideanNorm (z - 0) < 8 * R}])
          (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal A) ∧
        (eLpNorm (fun ω => frobeniusNorm (fun j k => S Q R i ω 0 j k -
          (reducedEnvironmentLaw Q)[fun a => S Q R i a 0 j k |
            reducedCoefficientObservationSigma
              {z : Vec 2 | euclideanNorm (z - 0) < 8 * R}] ω))
          (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal A))


include hS hSm hSsk hSn huc hSc hgradientTail hplanarTail

/-- The measurable normalized scalar source is constructed, with no scalar
source-existence premise. The selected representative's planar continuity
and the listed skew and tail requirements remain internal obligations.
Source: `paper/main.tex:895–977`. -/
theorem correctorLocalConstruction_of_selected_scalar_and_skew_sources_and_tails
    (h45 : ScalarStationaryEstimate) (h46 : ScalarPlanarL2Estimate)
    (h47 : ScalarHeatDifferenceEstimate) (h68 : FluxGradientEstimate)
    (h614 : FluxStationaryEstimate) (h615 : FluxPlanarL2Estimate)
    (h616 : FluxHeatDifferenceEstimate)
    (h817 : LocalBoundednessEstimate) (h832 : InteriorGradientEstimate)
    (h836 : InteriorRegularRepresentative) (hH2 : CorrectorWeakH2) :
    CorrectorLocalConstruction := by
  exact correctorLocalConstruction_of_dimensionwise_sources_and_tails
    (selectedCanonicalScalarSource hP) S (selectedCanonicalScalarSource_normalized hP)
    hS hSm hSsk hSn huc hSc hgradientTail hplanarTail
    h45 h46 h47 h68 h614 h615 h616 hP h817 h832 h836 hH2

end EinsteinRelation
