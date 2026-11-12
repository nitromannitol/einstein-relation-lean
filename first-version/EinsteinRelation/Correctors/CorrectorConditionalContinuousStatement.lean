import EinsteinRelation.Correctors.CorrectorConditionalStatement

/-! # Continuous-representative statement of Lemma 5.2

Source: `paper/main.tex:770–786`. Spatial continuity fixes the point
values of the scalar and skew representatives used in the centered
observables. This proposition records the successor interface; it does
not assert a proof. The uniform constant and both conclusions are those
of the original production statement.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace EinsteinRelation.Correctors
open NormalizedSpatialRepresentativeSupport
open NormalizedScalarPhysicalLawTransportSupport HeatSelectedSkewMeaning

attribute [local instance] ReductionImageV3.fieldPair_standardBorel
local instance continuousRestrictionMeasurableSpace {d : ℕ} (U : Set (Vec d)) :
    MeasurableSpace C(U, Mat d) := borel C(U, Mat d)

/-- Lemma 5.2 for continuous scalar and skew representatives, with the
uniform constant preceding the environment law. Source: `paper/main.tex:774–786`. -/
def CorrectorConditionalContinuousStatement : Prop :=
  ∀ (d : ℕ) [Fact (2 ≤ d)] (Λ₀ r₀ : ℝ) (ζ : SourceMollifier d) (m : ℝ), 2 ≤ m → ∃ C : ℝ,
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (R : ℝ) (hR : 1 ≤ R) (y : Point d) (i : Fin d)
      (φ : FieldPair d → Point d → ℝ) (σ : FieldPair d → Vec d → Mat d),
      IsNormalizedCanonicalScalarCorrector Q i ζ R hR y φ →
      HasHeatSelectedSkewCorrectorColumn (Fact.out : 2 ≤ d) Q i σ →
      (∀ᵐ ω ∂reducedEnvironmentLaw Q, Continuous (φ ω) ∧ Continuous (σ ω)) →
      let μ := reducedEnvironmentLaw Q
      let obsSigma := Carriers.reducedCoefficientObservationSigma (conditionalCorrectorBall R y)
      let grad := conditionalCorrectorGradient Q i y
      let cφ := conditionalCenteredScalar ζ R y φ
      let cσ := conditionalCenteredSkew ζ R y σ
      eLpNorm (fun ω => euclideanNorm (grad ω - condExp obsSigma μ grad ω))
          (ENNReal.ofReal m) μ ≤ ENNReal.ofReal (C * R ^ (-(d : ℝ) / 2)) ∧
      (d = 2 →
        eLpNorm (fun ω => cφ ω - condExp obsSigma μ cφ ω) (ENNReal.ofReal m) μ +
          eLpNorm (fun ω => frobeniusNorm (Matrix.of (fun a b =>
            cσ ω a b - condExp obsSigma μ (fun ω' => cσ ω' a b) ω)))
            (ENNReal.ofReal m) μ ≤ ENNReal.ofReal C)


end EinsteinRelation.Correctors
