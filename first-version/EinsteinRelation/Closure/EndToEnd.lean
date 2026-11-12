import EinsteinRelation.Closure.FromCorrectorInputs
import EinsteinRelation.Correctors.CorrectorLocalFromSelectedScalarCopyBounds
import EinsteinRelation.Mobility.CorrectorGradientMomentsFromFrozenInputs

/-! # The mobility bound from frozen inputs and the remaining corrector obligations

Source: `paper/main.tex:93–99,709–776,853–969`. The scalar source and
Lemma 5.1 gradient step are supplied by their providers. The skew source,
planar continuity and the two paired estimates remain explicit internal
obligations; this is a conditional composition, not a closure of those results.
-/

open MeasureTheory ProbabilityTheory Filter Topology
namespace EinsteinRelation.Closure
open Correctors External.AKM External.GilbargTrudinger HeatSelectedSkewMeaning
open Correctors.NormalizedSpatialRepresentativeSupport
open Correctors.NormalizedScalarPhysicalLawTransportSupport
local instance : Fact (2 ≤ (2 : ℕ)) := ⟨le_rfl⟩
attribute [local instance] ReductionImageV3.fieldPair_standardBorel
local instance endToEndRestrictionMeasurableSpace {d : ℕ} (U : Set (Vec d)) :
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
      1 ≤ R → ∀ i : Fin 2, ∀ᵐ ω ∂reducedEnvironmentLaw Q,
        Continuous (selectedCanonicalScalarSource hP Q R i ω))
    (hSc : ∀ {L r₀ : ℝ} (Q : EnvironmentLaw 2 L r₀) (R : ℝ),
      1 ≤ R → ∀ i : Fin 2, ∀ᵐ ω ∂reducedEnvironmentLaw Q, Continuous (S Q R i ω))
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
    (h836 : InteriorRegularRepresentative) (hH2 : CorrectorWeakH2)

include hP S hS hSm hSsk hSn huc hSc hgradient hplanar
  h45 h46 h47 h68 h614 h615 h616 h817 h832 h836 hH2

/-- Proposition 5.3's production construction from precisely the pending
source properties and copy estimates. Source: `paper/main.tex:887–969`. -/
theorem correctorLocalConstruction_end_to_end : CorrectorLocalConstruction := by
  exact correctorLocalConstruction_of_selected_scalar_and_separate_copy_bounds
    hP S hS hSm hSsk hSn huc hSc hgradient hplanar
    h45 h46 h47 h68 h614 h615 h616 h817 h832 h836 hH2

variable
    (hFOT : FukushimaDecompositionInput)
    (hGir : GirsanovEndpointStep) (hInv : UnforcedEnvironmentInvarianceStep)
    (hRF : External.GMPReducedFamilyExistence)
    (hE : GMPCouplingExistsV2Input) (hTail : GMPCouplingTailsV2Input)
    (hLoc : External.GMPKernelLocality)

include hFOT hGir hInv hRF hE hTail hLoc

/-- Theorem 1.2 with its exact GMP-family conclusion, conditional on the
listed frozen external inputs and the remaining internal corrector obligations.
Source: `paper/main.tex:93–99`. -/
theorem mobilityRate_end_to_end
    (hAKM : AKMFluxDecayLargeTime) (hRV : External.GMPReducedVelocityExistence)
    (hTC : External.GMPTimeChangeLaw) (hPos : External.GMPPhysicalVelocityPositive)
    (hErg : External.GMPEnvironmentProcessErgodic) (hIP : External.GMPReducedInvarianceAbar)
    (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) :
    ∃ C lamStar : ℝ, 0 < lamStar ∧
      ∀ (Q : EnvironmentLaw d Λ₀ r₀) (P : DiffusionFamily d),
      IsGMPPhysicalFamily hd Q.ellipticity_parameter Q P →
      ∀ (covariance : Mat d), HasDiffusivity Q.measure (originLaw (P 0)) covariance →
      ∀ (lam : ℝ), 0 < lam → lam ≤ lamStar →
      ∀ (velocity : Vec d), HasQuenchedVelocity Q.measure (originLaw (P lam)) velocity →
      euclideanNorm ((lam⁻¹ • velocity) - covariance.mulVec (unitVector (⟨0, by omega⟩ : Fin d)))
        ≤ C * lam := by
  have H53 := correctorLocalConstruction_end_to_end hP S hS hSm hSsk hSn huc hSc
    hgradient hplanar h45 h46 h47 h68 h614 h615 h616 h817 h832 h836 hH2
  have H51 := correctorGradientMoments_of_frozen_inputs
    h45 h46 h47 h68 h614 h615 h616 hP h817 h832 h836
  exact mobilityRateV4_of_corrector_inputs hFOT hGir hInv hRF hE hTail hLoc
    H53 H51 hAKM hRV hTC hPos hErg hIP d hd Λ₀ r₀

/-- Proposition 6.1 on production carriers with the same remaining
corrector obligations. Source: `paper/main.tex:970–989`. -/
theorem scalarDecomposition_end_to_end : ScalarDecompositionTwin := by
  have H53 := correctorLocalConstruction_end_to_end hP S hS hSm hSsk hSn huc hSc
    hgradient hplanar h45 h46 h47 h68 h614 h615 h616 h817 h832 h836 hH2
  have H51 := correctorGradientMoments_of_frozen_inputs
    h45 h46 h47 h68 h614 h615 h616 hP h817 h832 h836
  exact scalarDecompositionV2Twin_of_gmp_corrector_inputs
    hFOT hGir hInv hRF hE hTail hLoc H53 H51

end EinsteinRelation.Closure
