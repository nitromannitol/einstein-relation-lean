import EinsteinRelation.Correctors.CorrectorConditionalContinuousStatement
import EinsteinRelation.Correctors.ConditionalCopyPlanarMoments

/-! Source: `paper/main.tex:834-894`. These are internal analytic
obligations for the continuous version of Lemma 5.2. They are not external
inputs or proved consequences of the cited literature. In particular they
contain no conditional-expectation estimate or conclusion of Lemma 5.2. -/

open MeasureTheory
namespace EinsteinRelation.Correctors
open NormalizedSpatialRepresentativeSupport HeatSelectedSkewMeaning
open NormalizedScalarPhysicalLawTransportSupport

attribute [local instance] ReductionImageV3.fieldPair_standardBorel
local instance momentFact : Fact (2 ≤ 2) := ⟨by decide⟩
local instance conditionalMomentRestrictionMeasurableSpace {d : ℕ} (U : Set (Vec d)) :
    MeasurableSpace C(U, Mat d) := borel C(U, Mat d)

/-- The sharp point-gradient copy bound, the planar ball-energy bound,
and finite first absolute moments of centered marginal observables. The latter
follow from the continuous representatives and stationary L² energy in
`conditionalMomentInputs_of_pairEnergyBounds`; the two sharp bounds remain
internal obligations. The constants precede the environment law.
Source: `paper/main.tex:834-894`. -/
def ConditionalMomentInputs : Prop :=
  (∀ (d : ℕ) [Fact (2 ≤ d)] (L r₀ m : ℝ), 2 ≤ m →
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (Q : EnvironmentLaw d L r₀)
      (R : ℝ), 1 ≤ R → ∀ (y : Point d) (i : Fin d),
      eLpNorm (fun z : C(conditionalCorrectorBall R y, Mat d) ×
        (FieldPair d × FieldPair d) => euclideanNorm
        (conditionalCorrectorGradient Q i y z.2.1 - conditionalCorrectorGradient Q i y z.2.2))
        (ENNReal.ofReal m)
        (reducedConditionalCopyLaw (reducedEnvironmentLaw Q) (conditionalCorrectorBall R y)) ≤
          ENNReal.ofReal (B * R ^ (-(d : ℝ)/2))) ∧
  (∀ (L r₀ m : ℝ), 2 ≤ m → ∃ B : ℝ, 0 ≤ B ∧
    ∀ (Q : EnvironmentLaw 2 L r₀) (R : ℝ), 1 ≤ R → ∀ (y : Point 2) (i : Fin 2),
      MemLp (conditionalCopyGradientRms Q R y i) (ENNReal.ofReal m)
        (reducedConditionalCopyLaw (reducedEnvironmentLaw Q) (conditionalCorrectorBall R y)) ∧
      eLpNorm (conditionalCopyGradientRms Q R y i) (ENNReal.ofReal m)
        (reducedConditionalCopyLaw (reducedEnvironmentLaw Q) (conditionalCorrectorBall R y)) ≤
          ENNReal.ofReal (B/R)) ∧
  (∀ {L r₀ : ℝ} (Q : EnvironmentLaw 2 L r₀) (ζ : SourceMollifier 2)
    (R : ℝ) (hR : 1 ≤ R) (y : Point 2) (i : Fin 2)
    (φ : FieldPair 2 → Point 2 → ℝ) (σ : FieldPair 2 → Vec 2 → Mat 2),
    IsNormalizedCanonicalScalarCorrector Q i ζ R hR y φ →
    HasHeatSelectedSkewCorrectorColumn (by decide) Q i σ →
    (∀ᵐ ω ∂reducedEnvironmentLaw Q, Continuous (φ ω) ∧ Continuous (σ ω)) →
    HasFiniteIntegral (conditionalCenteredScalar ζ R y φ) (reducedEnvironmentLaw Q) ∧
      ∀ a b, HasFiniteIntegral (fun ω => conditionalCenteredSkew ζ R y σ ω a b)
        (reducedEnvironmentLaw Q))

end EinsteinRelation.Correctors
