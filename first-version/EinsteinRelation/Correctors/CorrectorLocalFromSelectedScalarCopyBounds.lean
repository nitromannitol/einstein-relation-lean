import EinsteinRelation.Correctors.CorrectorLocalFromSelectedScalar
import EinsteinRelation.Correctors.CanonicalSourceTailsFromConditional
import EinsteinRelation.Correctors.CorrectorConditionalFromSeparateCopyBounds

/-! # Proposition 5.3 from constructed scalar sources and paired bounds

Source: `paper/main.tex:774–786,895–977`. Conditional-copy Jensen supplies
both tails used in the fixed canonical mollifier fields. The analytic paired
bounds and the remaining skew/continuous-source construction are explicit.
-/

open MeasureTheory ProbabilityTheory
namespace EinsteinRelation
open Correctors External.AKM External.GilbargTrudinger HeatSelectedSkewMeaning
open Correctors.NormalizedSpatialRepresentativeSupport
open Correctors.NormalizedScalarPhysicalLawTransportSupport
local instance : Fact (2 ≤ (2 : ℕ)) := ⟨le_rfl⟩
attribute [local instance] ReductionImageV3.fieldPair_standardBorel
local instance copyRestrictionMeasurableSpace {d : ℕ} (U : Set (Vec d)) :
    MeasurableSpace C(U, Mat d) := borel C(U, Mat d)

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

include hS hSm hSsk hSn huc hSc

/-- Lemma 5.2 replaces the two separately supplied tail families; its
actual scalar/skew normalization is checked at the origin.
Source: `paper/main.tex:774–786,948–973`. -/
theorem correctorLocalConstruction_of_selected_scalar_and_conditional
    (h52 : CorrectorConditionalStatement)
    (h45 : ScalarStationaryEstimate) (h46 : ScalarPlanarL2Estimate)
    (h47 : ScalarHeatDifferenceEstimate) (h68 : FluxGradientEstimate)
    (h614 : FluxStationaryEstimate) (h615 : FluxPlanarL2Estimate)
    (h616 : FluxHeatDifferenceEstimate)
    (h817 : LocalBoundednessEstimate) (h832 : InteriorGradientEstimate)
    (h836 : InteriorRegularRepresentative) (hH2 : CorrectorWeakH2) :
    CorrectorLocalConstruction := by
  apply correctorLocalConstruction_of_selected_scalar_and_skew_sources_and_tails
    hP S hS hSm hSsk hSn huc hSc
    ?_ ?_ h45 h46 h47 h68 h614 h615 h616 h817 h832 h836 hH2
  · intro d _ L r₀ p hp
    exact canonical_gradient_origin_tail_of_correctorConditional h52 hP d L r₀ p hp
      (fun Q R hR i => ⟨S Q R i, hS Q R hR i⟩)
  · intro L r₀ p hp
    obtain ⟨A, hA, hb⟩ := canonical_planar_origin_tails_of_correctorConditional h52 hp
    exact ⟨A, hA, fun Q R hR i => hb Q R hR i
      (selectedCanonicalScalarSource hP Q R i) (S Q R i)
      (selectedCanonicalScalarSource_normalized hP Q R hR i)
      (hS Q R hR i) (hSn Q R hR i)⟩

/-- The remaining Lemma 5.2 hypotheses are precisely the paired gradient
bound and the centered planar scalar/skew bounds, with their measurable and
integrable observables. No conditional-tail conclusion is assumed separately.
Source: `paper/main.tex:861–894,948–973`. -/
theorem correctorLocalConstruction_of_selected_scalar_and_copy_bounds
    (hcopies : ∀ (d : ℕ) [Fact (2 ≤ d)] (Λ₀ r₀ : ℝ) (ζ : SourceMollifier d)
      (m : ℝ), 2 ≤ m → ∃ C : ℝ,
      ∀ (Q : EnvironmentLaw d Λ₀ r₀) (R : ℝ) (hR : 1 ≤ R) (y : Point d) (i : Fin d)
        (φ : FieldPair d → Point d → ℝ) (σ : FieldPair d → Vec d → Mat d),
        IsNormalizedCanonicalScalarCorrector Q i ζ R hR y φ →
        HasHeatSelectedSkewCorrectorColumn (Fact.out : 2 ≤ d) Q i σ →
        eLpNorm (fun z : C(conditionalCorrectorBall R y, Mat d) ×
          (FieldPair d × FieldPair d) =>
          euclideanNorm (conditionalCorrectorGradient Q i y z.2.1 -
            conditionalCorrectorGradient Q i y z.2.2)) (ENNReal.ofReal m)
          (reducedConditionalCopyLaw (reducedEnvironmentLaw Q) (conditionalCorrectorBall R y)) ≤
            ENNReal.ofReal (C * R ^ (-(d : ℝ) / 2)) ∧
        (d = 2 →
          Measurable (conditionalCenteredScalar ζ R y φ) ∧
          Integrable (conditionalCenteredScalar ζ R y φ) (reducedEnvironmentLaw Q) ∧
          Measurable (conditionalCenteredSkew ζ R y σ) ∧
          (∀ a b, Integrable (fun ω => conditionalCenteredSkew ζ R y σ ω a b)
            (reducedEnvironmentLaw Q)) ∧
          eLpNorm (fun z : C(conditionalCorrectorBall R y, Mat d) ×
            (FieldPair d × FieldPair d) =>
            conditionalCenteredScalar ζ R y φ z.2.1 - conditionalCenteredScalar ζ R y φ z.2.2)
            (ENNReal.ofReal m)
            (reducedConditionalCopyLaw (reducedEnvironmentLaw Q) (conditionalCorrectorBall R y)) +
          eLpNorm (fun z : C(conditionalCorrectorBall R y, Mat d) ×
            (FieldPair d × FieldPair d) =>
            frobeniusNorm (conditionalCenteredSkew ζ R y σ z.2.1 -
              conditionalCenteredSkew ζ R y σ z.2.2)) (ENNReal.ofReal m)
            (reducedConditionalCopyLaw (reducedEnvironmentLaw Q) (conditionalCorrectorBall R y)) ≤
              ENNReal.ofReal C))
    (h45 : ScalarStationaryEstimate) (h46 : ScalarPlanarL2Estimate)
    (h47 : ScalarHeatDifferenceEstimate) (h68 : FluxGradientEstimate)
    (h614 : FluxStationaryEstimate) (h615 : FluxPlanarL2Estimate)
    (h616 : FluxHeatDifferenceEstimate)
    (h817 : LocalBoundednessEstimate) (h832 : InteriorGradientEstimate)
    (h836 : InteriorRegularRepresentative) (hH2 : CorrectorWeakH2) :
    CorrectorLocalConstruction := by
  exact correctorLocalConstruction_of_selected_scalar_and_conditional hP S
    hS hSm hSsk hSn huc hSc (correctorConditional_of_uniform_copy_bounds hcopies)
    h45 h46 h47 h68 h614 h615 h616 h817 h832 h836 hH2

/-- The final assembly exposes the two independent open Lemma 5.2 pieces,
rather than requiring a shared copy-bound constant.
Source: `paper/main.tex:861–894,948–973`. -/
theorem correctorLocalConstruction_of_selected_scalar_and_separate_copy_bounds
    (hgradient : ∀ (d : ℕ) [Fact (2 ≤ d)] (Λ₀ r₀ m : ℝ),
      2 ≤ m → ∃ C : ℝ, ∀ (Q : EnvironmentLaw d Λ₀ r₀) (R : ℝ), 1 ≤ R →
        ∀ (y : Point d) (i : Fin d),
        eLpNorm (fun z : C(conditionalCorrectorBall R y, Mat d) ×
          (FieldPair d × FieldPair d) =>
          euclideanNorm (conditionalCorrectorGradient Q i y z.2.1 -
            conditionalCorrectorGradient Q i y z.2.2)) (ENNReal.ofReal m)
          (reducedConditionalCopyLaw (reducedEnvironmentLaw Q) (conditionalCorrectorBall R y)) ≤
            ENNReal.ofReal (C * R ^ (-(d : ℝ) / 2)))
    (hplanar : ∀ (d : ℕ) [Fact (2 ≤ d)] (Λ₀ r₀ : ℝ) (ζ : SourceMollifier d)
      (m : ℝ), 2 ≤ m → ∃ C : ℝ,
      ∀ (Q : EnvironmentLaw d Λ₀ r₀) (R : ℝ) (hR : 1 ≤ R) (y : Point d) (i : Fin d)
        (φ : FieldPair d → Point d → ℝ) (σ : FieldPair d → Vec d → Mat d),
        IsNormalizedCanonicalScalarCorrector Q i ζ R hR y φ →
        HasHeatSelectedSkewCorrectorColumn (Fact.out : 2 ≤ d) Q i σ →
        (d = 2 →
          Measurable (conditionalCenteredScalar ζ R y φ) ∧
          Integrable (conditionalCenteredScalar ζ R y φ) (reducedEnvironmentLaw Q) ∧
          Measurable (conditionalCenteredSkew ζ R y σ) ∧
          (∀ a b, Integrable (fun ω => conditionalCenteredSkew ζ R y σ ω a b)
            (reducedEnvironmentLaw Q)) ∧
          eLpNorm (fun z : C(conditionalCorrectorBall R y, Mat d) ×
            (FieldPair d × FieldPair d) =>
            conditionalCenteredScalar ζ R y φ z.2.1 - conditionalCenteredScalar ζ R y φ z.2.2)
            (ENNReal.ofReal m)
            (reducedConditionalCopyLaw (reducedEnvironmentLaw Q) (conditionalCorrectorBall R y)) +
          eLpNorm (fun z : C(conditionalCorrectorBall R y, Mat d) ×
            (FieldPair d × FieldPair d) =>
            frobeniusNorm (conditionalCenteredSkew ζ R y σ z.2.1 -
              conditionalCenteredSkew ζ R y σ z.2.2)) (ENNReal.ofReal m)
            (reducedConditionalCopyLaw (reducedEnvironmentLaw Q) (conditionalCorrectorBall R y)) ≤
              ENNReal.ofReal C))

    (h45 : ScalarStationaryEstimate) (h46 : ScalarPlanarL2Estimate)
    (h47 : ScalarHeatDifferenceEstimate) (h68 : FluxGradientEstimate)
    (h614 : FluxStationaryEstimate) (h615 : FluxPlanarL2Estimate)
    (h616 : FluxHeatDifferenceEstimate)
    (h817 : LocalBoundednessEstimate) (h832 : InteriorGradientEstimate)
    (h836 : InteriorRegularRepresentative) (hH2 : CorrectorWeakH2) :
    CorrectorLocalConstruction := by
  exact correctorLocalConstruction_of_selected_scalar_and_conditional hP S
    hS hSm hSsk hSn huc hSc
    (correctorConditional_of_separate_copy_bounds hgradient hplanar)
    h45 h46 h47 h68 h614 h615 h616 h817 h832 h836 hH2

end EinsteinRelation
