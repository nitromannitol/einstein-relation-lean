import EinsteinRelation.Correctors.CorrectorLocalFromContinuousNormalizedSources
import EinsteinRelation.Correctors.SelectedContinuousScalarSource

/-! # Proposition 5.3 with a proved continuous scalar selection

Source: `paper/main.tex:774–786,895–977`. The planar copy estimate is used
only for the jointly measurable selected scalar and skew sources at the
origin. No estimate for arbitrary spatial representatives is required.
-/

open MeasureTheory ProbabilityTheory
namespace EinsteinRelation
open Correctors External.AKM External.GilbargTrudinger HeatSelectedSkewMeaning
open Correctors.NormalizedSpatialRepresentativeSupport
open Correctors.NormalizedScalarPhysicalLawTransportSupport
local instance : Fact (2 ≤ (2 : ℕ)) := ⟨le_rfl⟩
attribute [local instance] ReductionImageV3.fieldPair_standardBorel
local instance regularCopyRestrictionMeasurableSpace {d : ℕ} (U : Set (Vec d)) :
    MeasurableSpace C(U, Mat d) := borel C(U, Mat d)

variable
    (hP : BallPoincareEstimate)
    (h836 : InteriorRegularRepresentative)
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
    (hSc : ∀ {L r₀ : ℝ} (Q : EnvironmentLaw 2 L r₀) (R : ℝ),
      1 ≤ R → ∀ i : Fin 2, ∀ᵐ ω ∂reducedEnvironmentLaw Q, Continuous (S Q R i ω))


include hS hSm hSsk hSn hSc

/-- The selected-family form of Proposition 5.3. All remaining internal
source and paired-bound obligations are explicit.
Source: `paper/main.tex:861–894,948–973`. -/
theorem correctorLocalConstruction_of_selected_regular_sources_and_separate_copy_bounds
    (hgradient : ∀ (d : ℕ) [Fact (2 ≤ d)] (Λ₀ r₀ m : ℝ),
      2 ≤ m → ∃ C : ℝ, ∀ (Q : EnvironmentLaw d Λ₀ r₀) (R : ℝ), 1 ≤ R →
        ∀ (y : Point d) (i : Fin d),
        eLpNorm (fun z : C(conditionalCorrectorBall R y, Mat d) ×
          (FieldPair d × FieldPair d) =>
          euclideanNorm (conditionalCorrectorGradient Q i y z.2.1 -
            conditionalCorrectorGradient Q i y z.2.2)) (ENNReal.ofReal m)
          (reducedConditionalCopyLaw (reducedEnvironmentLaw Q) (conditionalCorrectorBall R y)) ≤
            ENNReal.ofReal (C * R ^ (-(d : ℝ) / 2)))
    (hplanar : ∀ (L r₀ m : ℝ), 2 ≤ m → ∃ C : ℝ,
      ∀ (Q : EnvironmentLaw 2 L r₀) (R : ℝ) (_hR : 1 ≤ R) (i : Fin 2),
        let φ := fun ω x => selectedContinuousCanonicalScalarSource hP h836 Q R i ω x.ofLp
        let σ := S Q R i
        Measurable (conditionalCenteredScalar (canonicalSourceMollifier 2) R 0 φ) ∧
        Integrable (conditionalCenteredScalar (canonicalSourceMollifier 2) R 0 φ)
          (reducedEnvironmentLaw Q) ∧
        Measurable (conditionalCenteredSkew (canonicalSourceMollifier 2) R 0 σ) ∧
        (∀ a b, Integrable (fun ω =>
          conditionalCenteredSkew (canonicalSourceMollifier 2) R 0 σ ω a b)
          (reducedEnvironmentLaw Q)) ∧
        eLpNorm (fun z : C(conditionalCorrectorBall R (0 : Point 2), Mat 2) ×
          (FieldPair 2 × FieldPair 2) =>
          conditionalCenteredScalar (canonicalSourceMollifier 2) R 0 φ z.2.1 -
            conditionalCenteredScalar (canonicalSourceMollifier 2) R 0 φ z.2.2)
          (ENNReal.ofReal m)
          (reducedConditionalCopyLaw (reducedEnvironmentLaw Q) (conditionalCorrectorBall R 0)) +
        eLpNorm (fun z : C(conditionalCorrectorBall R (0 : Point 2), Mat 2) ×
          (FieldPair 2 × FieldPair 2) =>
          frobeniusNorm (conditionalCenteredSkew (canonicalSourceMollifier 2) R 0 σ z.2.1 -
            conditionalCenteredSkew (canonicalSourceMollifier 2) R 0 σ z.2.2))
          (ENNReal.ofReal m)
          (reducedConditionalCopyLaw (reducedEnvironmentLaw Q) (conditionalCorrectorBall R 0)) ≤
            ENNReal.ofReal C)
    (h45 : ScalarStationaryEstimate) (h46 : ScalarPlanarL2Estimate)
    (h47 : ScalarHeatDifferenceEstimate) (h68 : FluxGradientEstimate)
    (h614 : FluxStationaryEstimate) (h615 : FluxPlanarL2Estimate)
    (h616 : FluxHeatDifferenceEstimate)
    (h817 : LocalBoundednessEstimate) (h832 : InteriorGradientEstimate)
    (hH2 : CorrectorWeakH2) :
    CorrectorLocalConstruction := by
  exact correctorLocalConstruction_of_continuous_normalized_sources_and_separate_copy_bounds
    hP (fun Q R i => selectedContinuousCanonicalScalarSource hP h836 Q R i) S
    (fun Q R hR i => selectedContinuousCanonicalScalarSource_normalized hP h836 Q R hR i)
    hS hSm hSsk hSn
    (fun Q R _ i => ae_continuous_selectedContinuousCanonicalScalarSource hP h836 Q R i)
    hSc hgradient hplanar
    h45 h46 h47 h68 h614 h615 h616 h817 h832 h836 hH2

end EinsteinRelation
