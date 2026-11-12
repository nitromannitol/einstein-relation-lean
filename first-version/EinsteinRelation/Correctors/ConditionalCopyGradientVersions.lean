import EinsteinRelation.Correctors.CanonicalContinuousGradientIdentification
import EinsteinRelation.Correctors.ConditionalCopyRecentering

/-! # Actual paired observables of a continuous gradient version

Source: `paper/main.tex:834–875,886–894`. Both fixed-point differences
and normalized spatial energies use the canonical gradient on the actual
copy law. The energy identity only requires spatial a.e. identification;
the point identity uses the proved continuous-version identification.
-/

open MeasureTheory
open scoped ENNReal

namespace EinsteinRelation.Correctors
open External.AKM NormalizedSpatialRepresentativeSupport

attribute [local instance] ReductionImageV3.fieldPair_standardBorel
local instance gradientVersionRestrictionMeasurableSpace {d : ℕ} (U : Set (Vec d)) :
    MeasurableSpace C(U, Mat d) := borel C(U, Mat d)

/-- Spatial energy of any identified gradient version equals the literal
canonical paired energy under the actual conditional copies. Continuity
and pointwise covariance are unnecessary for this identity.
Source: `paper/main.tex:834–861,886–894`. -/
theorem ae_conditionalCopy_vectorRms_gradient_version
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (g : FieldPair d → Vec d → Vec d)
    (hid : ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      g ω =ᵐ[volume] fun x => conditionalCorrectorGradient Q i (WithLp.toLp 2 x) ω)
    (U : Set (Vec d)) (hU : IsOpen U) (V : Set (Vec d)) :
    (fun z : C(U, Mat d) × (FieldPair d × FieldPair d) =>
      vectorRms volume V (fun x => g z.2.1 x - g z.2.2 x))
      =ᵐ[reducedConditionalCopyLaw (reducedEnvironmentLaw Q) U]
    (fun z => vectorRms volume V (fun x =>
      conditionalCorrectorGradient Q i (WithLp.toLp 2 x) z.2.1 -
        conditionalCorrectorGradient Q i (WithLp.toLp 2 x) z.2.2)) := by
  obtain ⟨_, hfirst, hsecond, _⟩ :=
    reducedConditionalCopy_properties (reducedEnvironmentLaw Q) U hU
  have hmp₁ : MeasurePreserving
      (fun z : C(U, Mat d) × (FieldPair d × FieldPair d) => z.2.1)
      (reducedConditionalCopyLaw (reducedEnvironmentLaw Q) U)
      (reducedEnvironmentLaw Q) := ⟨measurable_snd.fst, hfirst⟩
  have hmp₂ : MeasurePreserving
      (fun z : C(U, Mat d) × (FieldPair d × FieldPair d) => z.2.2)
      (reducedConditionalCopyLaw (reducedEnvironmentLaw Q) U)
      (reducedEnvironmentLaw Q) := ⟨measurable_snd.snd, hsecond⟩
  filter_upwards [hmp₁.quasiMeasurePreserving.ae hid,
    hmp₂.quasiMeasurePreserving.ae hid] with z h₁ h₂
  unfold vectorRms
  congr 1
  rw [setAverage_eq, setAverage_eq]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae h₁, ae_restrict_of_ae h₂] with x hx₁ hx₂
  rw [hx₁, hx₂]

/-- At each prescribed center the continuous-version copy difference has
exactly the production canonical-gradient seminorm. No new representative
equality or uniqueness hypothesis is assumed.
Source: `paper/main.tex:861–875,886–894`. -/
theorem eLpNorm_conditionalCopy_continuous_gradient_version
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (g : FieldPair d → Vec d → Vec d)
    (hm : Measurable (fun z : FieldPair d × Vec d => g z.1 z.2))
    (hc : ∀ᵐ ω ∂reducedEnvironmentLaw Q, Continuous (g ω))
    (hid : ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      g ω =ᵐ[volume] fun x => conditionalCorrectorGradient Q i (WithLp.toLp 2 x) ω)
    (R : ℝ) (y : Point d) (p : ℝ≥0∞) :
    eLpNorm (fun z : C(conditionalCorrectorBall R y, Mat d) ×
      (FieldPair d × FieldPair d) => euclideanNorm (g z.2.1 y.ofLp - g z.2.2 y.ofLp)) p
      (reducedConditionalCopyLaw (reducedEnvironmentLaw Q) (conditionalCorrectorBall R y)) =
    eLpNorm (fun z : C(conditionalCorrectorBall R y, Mat d) ×
      (FieldPair d × FieldPair d) => euclideanNorm
        (conditionalCorrectorGradient Q i y z.2.1 - conditionalCorrectorGradient Q i y z.2.2)) p
      (reducedConditionalCopyLaw (reducedEnvironmentLaw Q) (conditionalCorrectorBall R y)) := by
  have heq := ae_continuous_version_eq_conditionalCorrectorGradient Q i g hm hc hid y
  obtain ⟨_, hfirst, hsecond, _⟩ := reducedConditionalCopy_properties
    (reducedEnvironmentLaw Q) (conditionalCorrectorBall R y) (isOpen_conditionalCorrectorBall R y)
  have hmp₁ : MeasurePreserving
      (fun z : C(conditionalCorrectorBall R y, Mat d) × (FieldPair d × FieldPair d) => z.2.1)
      (reducedConditionalCopyLaw (reducedEnvironmentLaw Q) (conditionalCorrectorBall R y))
      (reducedEnvironmentLaw Q) := ⟨measurable_snd.fst, hfirst⟩
  have hmp₂ : MeasurePreserving
      (fun z : C(conditionalCorrectorBall R y, Mat d) × (FieldPair d × FieldPair d) => z.2.2)
      (reducedConditionalCopyLaw (reducedEnvironmentLaw Q) (conditionalCorrectorBall R y))
      (reducedEnvironmentLaw Q) := ⟨measurable_snd.snd, hsecond⟩
  apply eLpNorm_congr_ae
  filter_upwards [hmp₁.quasiMeasurePreserving.ae heq,
    hmp₂.quasiMeasurePreserving.ae heq] with z h₁ h₂
  rw [h₁, h₂]

end EinsteinRelation.Correctors
