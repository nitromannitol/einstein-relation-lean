import EinsteinRelation.Correctors.CanonicalGradientConditionalEuclidean
import EinsteinRelation.Correctors.NormalizedScalarPhysicalLawTransportSupport
import EinsteinRelation.Correctors.HeatSelectedSkewMeaningSupport
import EinsteinRelation.Environment.MatrixNorm

/-! # Production statement and observables for Lemma 5.2

Source: `paper/main.tex:762–776`. The predicates below use the production
definitions of the normalized scalar corrector and heat-selected skew
corrector, whose bodies match the corresponding frozen definitions.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace EinsteinRelation.Correctors
open NormalizedSpatialRepresentativeSupport StationarySpatialRealization
open NormalizedScalarPhysicalLawTransportSupport HeatSelectedSkewMeaning

attribute [local instance] ReductionImageV3.fieldPair_standardBorel

local instance restrictionMeasurableSpace {d : ℕ} (U : Set (Vec d)) :
    MeasurableSpace C(U, Mat d) := borel C(U, Mat d)

/-- The actual conditional-copy law for coefficient observation on an open
set. Source: `paper/main.tex:878–886`. -/
noncomputable def reducedConditionalCopyLaw {d : ℕ}
    (μ : Measure (FieldPair d)) [IsProbabilityMeasure μ] (U : Set (Vec d)) :
    Measure (C(U, Mat d) × (FieldPair d × FieldPair d)) :=
  (μ.map (reducedCoefficientRestriction U)) ⊗ₘ
    (condDistrib (id : FieldPair d → FieldPair d) (reducedCoefficientRestriction U) μ ×ₖ
      condDistrib (id : FieldPair d → FieldPair d) (reducedCoefficientRestriction U) μ)

/-- The observed ball in the literal coordinate carrier.
Source: `paper/main.tex:766–768`. -/
def conditionalCorrectorBall {d : ℕ} (R : ℝ) (y : Point d) : Set (Vec d) :=
  (fun x : Vec d => (WithLp.toLp 2 x : Point d)) ⁻¹' Metric.ball y (8 * R)

/-- The source observation ball is open in the coordinate carrier.
Source: `paper/main.tex:764–768`. -/
theorem isOpen_conditionalCorrectorBall {d : ℕ} (R : ℝ) (y : Point d) :
    IsOpen (conditionalCorrectorBall R y) :=
  Metric.isOpen_ball.preimage (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ))

/-- The canonical stationary gradient at the requested point.
Source: `paper/main.tex:766–768`. -/
noncomputable def conditionalCorrectorGradient {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (y : Point d) : FieldPair d → Vec d :=
  fun ω => (spatialRealization (canonicalCorrectorGradient Q i :
    Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) (WithLp.ofLp y, ω)).ofLp

/-- Scalar centering by the source mollifier.
Source: `paper/main.tex:762–764,770–776`. -/
noncomputable def conditionalCenteredScalar {d : ℕ} (ζ : SourceMollifier d)
    (R : ℝ) (y : Point d) (φ : FieldPair d → Point d → ℝ) : FieldPair d → ℝ :=
  fun ω => φ ω y - ∫ z, sourceScaledMollifierKernel ζ R y z * φ ω z ∂volume

/-- Entrywise tensor centering by the source mollifier.
Source: `paper/main.tex:762–764,770–776`. -/
noncomputable def conditionalCenteredSkew {d : ℕ} (ζ : SourceMollifier d)
    (R : ℝ) (y : Point d) (σ : FieldPair d → Vec d → Mat d) : FieldPair d → Mat d :=
  fun ω => Matrix.of (fun a b => σ ω (WithLp.ofLp y) a b -
    ∫ z, sourceScaledMollifierKernel ζ R y z * σ ω (WithLp.ofLp z) a b ∂volume)

/-- The full Lemma 5.2 statement on production carriers. This proposition
alone asserts no proof. Its uniform constant precedes the environment law.
Source: `paper/main.tex:766–776`. -/
def CorrectorConditionalStatement : Prop :=
  ∀ (d : ℕ) [Fact (2 ≤ d)] (Λ₀ r₀ : ℝ) (ζ : SourceMollifier d) (m : ℝ), 2 ≤ m → ∃ C : ℝ,
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (R : ℝ) (hR : 1 ≤ R) (y : Point d) (i : Fin d)
      (φ : FieldPair d → Point d → ℝ) (σ : FieldPair d → Vec d → Mat d),
      IsNormalizedCanonicalScalarCorrector Q i ζ R hR y φ →
      HasHeatSelectedSkewCorrectorColumn (Fact.out : 2 ≤ d) Q i σ →
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
