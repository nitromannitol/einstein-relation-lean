import EinsteinRelation.Correctors.CanonicalGradientRegularRepresentative
import EinsteinRelation.Correctors.ConditionalCopyGradientVersions

/-! # A continuous canonical gradient for the conditional-copy estimate

Source: `paper/main.tex:735–737,860–875`. GT regularity and shrinking
averages construct the version. Stationarity identifies its prescribed
point values with the canonical variational gradient.
-/

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace EinsteinRelation.Correctors
open External.GilbargTrudinger NormalizedSpatialRepresentativeSupport

attribute [local instance] ReductionImageV3.fieldPair_standardBorel
local instance continuousGradientRestrictionMeasurableSpace {d : ℕ} (U : Set (Vec d)) :
    MeasurableSpace C(U, Mat d) := borel C(U, Mat d)

/-- The regular affine gradient with its deterministic affine part removed.
Source: `paper/main.tex:694–704,735–737`. -/
def continuousCanonicalGradient {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) (ω : FieldPair d) (x : Vec d) : Vec d :=
  canonicalAffineGradientRegularRepresentative Q i ω x - unitVector i

/-- The constructed gradient is jointly measurable.
Source: `paper/main.tex:860–875`. -/
theorem measurable_continuousCanonicalGradient {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    Measurable (fun z : FieldPair d × Vec d => continuousCanonicalGradient Q i z.1 z.2) :=
  ((measurable_canonicalAffineGradientRegularRepresentative Q i).comp measurable_swap).sub
    measurable_const

/-- The constructed version is continuous and represents the actual spatial
canonical gradient on a common full-probability event.
Source: `paper/main.tex:735–737,860–875`. -/
theorem ae_continuousCanonicalGradient
    (hP : BallPoincareEstimate) (h836 : InteriorRegularRepresentative)
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      Continuous (continuousCanonicalGradient Q i ω) ∧
      continuousCanonicalGradient Q i ω =ᵐ[volume]
        fun x => conditionalCorrectorGradient Q i (WithLp.toLp 2 x) ω := by
  filter_upwards [ae_canonicalAffineGradientRegularRepresentative hP h836 Q i] with ω hω
  refine ⟨hω.1.sub continuous_const, ?_⟩
  filter_upwards [hω.2] with x hx
  dsimp only [continuousCanonicalGradient]
  rw [← hx]
  simp only [add_sub_cancel_left, conditionalCorrectorGradient,
    StationarySpatialRealization.spatialRealization]

/-- At a prescribed point the regular version has the canonical value almost
surely. The exceptional event may depend on that point.
Source: `paper/main.tex:860–875`. -/
theorem ae_continuousCanonicalGradient_eq_conditionalCorrectorGradient
    (hP : BallPoincareEstimate) (h836 : InteriorRegularRepresentative)
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (y : Point d) :
    (fun ω => continuousCanonicalGradient Q i ω y.ofLp) =ᵐ[reducedEnvironmentLaw Q]
      conditionalCorrectorGradient Q i y :=
  ae_continuous_version_eq_conditionalCorrectorGradient Q i _
    (measurable_continuousCanonicalGradient Q i)
    ((ae_continuousCanonicalGradient hP h836 Q i).mono fun _ h => h.1)
    ((ae_continuousCanonicalGradient hP h836 Q i).mono fun _ h => h.2) y

/-- The continuous version's copy seminorm is exactly the unchanged production
observable; no regularity or version-identification premise remains.
Source: `paper/main.tex:861–875,886–894`. -/
theorem eLpNorm_conditionalCopy_continuousCanonicalGradient
    (hP : BallPoincareEstimate) (h836 : InteriorRegularRepresentative)
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (R : ℝ) (y : Point d) (p : ℝ≥0∞) :
    eLpNorm (fun z : C(conditionalCorrectorBall R y, Mat d) ×
      (FieldPair d × FieldPair d) => euclideanNorm
        (continuousCanonicalGradient Q i z.2.1 y.ofLp -
          continuousCanonicalGradient Q i z.2.2 y.ofLp)) p
      (reducedConditionalCopyLaw (reducedEnvironmentLaw Q) (conditionalCorrectorBall R y)) =
    eLpNorm (fun z : C(conditionalCorrectorBall R y, Mat d) ×
      (FieldPair d × FieldPair d) => euclideanNorm
        (conditionalCorrectorGradient Q i y z.2.1 - conditionalCorrectorGradient Q i y z.2.2)) p
      (reducedConditionalCopyLaw (reducedEnvironmentLaw Q) (conditionalCorrectorBall R y)) :=
  eLpNorm_conditionalCopy_continuous_gradient_version Q i _
    (measurable_continuousCanonicalGradient Q i)
    ((ae_continuousCanonicalGradient hP h836 Q i).mono fun _ h => h.1)
    ((ae_continuousCanonicalGradient hP h836 Q i).mono fun _ h => h.2) R y p

end EinsteinRelation.Correctors
