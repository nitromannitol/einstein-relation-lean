import EinsteinRelation.Correctors.ConditionalCopyPlanarAmplitude
import EinsteinRelation.Correctors.ConditionalCenteredMeasurability
import EinsteinRelation.Correctors.PlanarJointMomentComparison
import Mathlib.MeasureTheory.Group.Arithmetic

/-! Probability moments of the literal paired planar amplitudes.
Source: `paper/main.tex:872–894`. The paired spatial energy is an explicit
internal obligation; this file does not declare it a literature input. -/
open MeasureTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger NormalizedSpatialRepresentativeSupport
open NormalizedScalarPhysicalLawTransportSupport HeatSelectedSkewMeaning
attribute [local instance] ReductionImageV3.fieldPair_standardBorel
local instance planarMomentsDim : Fact (2 ≤ 2) := ⟨by decide⟩
local instance planarMomentsRestrictionMeasurableSpace {d : ℕ} (U : Set (Vec d)) : MeasurableSpace C(U, Mat d) := borel C(U, Mat d)

/-- The actual paired spatial energy with the same center and observation
as the source conditional copies. Source: `paper/main.tex:872–883`. -/
noncomputable def conditionalCopyGradientRms {L r₀ : ℝ} (Q : EnvironmentLaw 2 L r₀)
    (R : ℝ) (y : Point 2) (i : Fin 2)
    (z : C(conditionalCorrectorBall R y, Mat 2) × (FieldPair 2 × FieldPair 2)) : ℝ :=
  vectorRms volume (ball 0 (2*R)) (fun x =>
    conditionalCorrectorGradient Q i (WithLp.toLp 2 (x+y.ofLp)) z.2.1 -
      conditionalCorrectorGradient Q i (WithLp.toLp 2 (x+y.ofLp)) z.2.2)

/-- Sharp paired energy decay cancels the planar amplitude's factor of R.
All constants precede the environment, center, radius and corrector fields.
The joint skew measurability and spatial continuity concern the actual
fields in the conclusion. Source: `paper/main.tex:872–894`. -/
theorem paired_planar_centered_moments_of_energy
    (h817 : LocalBoundednessEstimate) (hP : BallPoincareEstimate) (L : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {r₀ : ℝ} (Q : EnvironmentLaw 2 L r₀)
      (ζ : SourceMollifier 2) (R : ℝ) (hR : 1 ≤ R) (y : Point 2) (i : Fin 2)
      (φ : FieldPair 2 → Point 2 → ℝ) (σ : FieldPair 2 → Vec 2 → Mat 2),
      IsNormalizedCanonicalScalarCorrector Q i ζ R hR y φ →
      HasHeatSelectedSkewCorrectorColumn (by decide) Q i σ →
      (∀ᵐ ω ∂reducedEnvironmentLaw Q, Continuous (φ ω) ∧ Continuous (σ ω)) →
      (∀ a b, Measurable (fun z : FieldPair 2 × Vec 2 => σ z.1 z.2 a b)) →
      ∀ (p : ℝ≥0∞) (B : ℝ), 0 ≤ B →
      MemLp (conditionalCopyGradientRms Q R y i) p
        (reducedConditionalCopyLaw (reducedEnvironmentLaw Q) (conditionalCorrectorBall R y)) →
      eLpNorm (conditionalCopyGradientRms Q R y i) p
        (reducedConditionalCopyLaw (reducedEnvironmentLaw Q) (conditionalCorrectorBall R y)) ≤
          ENNReal.ofReal (B/R) →
      Measurable (conditionalCenteredScalar ζ R y φ) ∧
      Measurable (conditionalCenteredSkew ζ R y σ) ∧
      MemLp (fun z : C(conditionalCorrectorBall R y, Mat 2) × (FieldPair 2 × FieldPair 2) =>
        conditionalCenteredScalar ζ R y φ z.2.1 - conditionalCenteredScalar ζ R y φ z.2.2) p
        (reducedConditionalCopyLaw (reducedEnvironmentLaw Q) (conditionalCorrectorBall R y)) ∧
      MemLp (fun z : C(conditionalCorrectorBall R y, Mat 2) × (FieldPair 2 × FieldPair 2) =>
        frobeniusNorm (conditionalCenteredSkew ζ R y σ z.2.1 -
          conditionalCenteredSkew ζ R y σ z.2.2)) p
        (reducedConditionalCopyLaw (reducedEnvironmentLaw Q) (conditionalCorrectorBall R y)) ∧
      eLpNorm (fun z : C(conditionalCorrectorBall R y, Mat 2) × (FieldPair 2 × FieldPair 2) =>
        conditionalCenteredScalar ζ R y φ z.2.1 - conditionalCenteredScalar ζ R y φ z.2.2) p
        (reducedConditionalCopyLaw (reducedEnvironmentLaw Q) (conditionalCorrectorBall R y)) +
      eLpNorm (fun z : C(conditionalCorrectorBall R y, Mat 2) × (FieldPair 2 × FieldPair 2) =>
        frobeniusNorm (conditionalCenteredSkew ζ R y σ z.2.1 -
          conditionalCenteredSkew ζ R y σ z.2.2)) p
        (reducedConditionalCopyLaw (reducedEnvironmentLaw Q) (conditionalCorrectorBall R y)) ≤
          ENNReal.ofReal (C*B) := by
  obtain ⟨C, hC, hb⟩ := ae_paired_planar_centered_correctors_le_energy h817 hP L
  refine ⟨2*C, by positivity, ?_⟩
  intro r₀ Q ζ R hR y i φ σ hφ hσ hc hσm p B hB hE hEb
  have hRp : 0 < R := zero_lt_one.trans_le hR
  obtain ⟨hφm, hSm⟩ := measurable_conditionalCentered_of_joint ζ R y φ σ hφ.1 hσm
  let ν := reducedConditionalCopyLaw (reducedEnvironmentLaw Q) (conditionalCorrectorBall R y)
  let f := fun z : C(conditionalCorrectorBall R y, Mat 2) × (FieldPair 2 × FieldPair 2) =>
    conditionalCenteredScalar ζ R y φ z.2.1 - conditionalCenteredScalar ζ R y φ z.2.2
  let g := fun z : C(conditionalCorrectorBall R y, Mat 2) × (FieldPair 2 × FieldPair 2) =>
    frobeniusNorm (conditionalCenteredSkew ζ R y σ z.2.1 -
      conditionalCenteredSkew ζ R y σ z.2.2)
  have hfm : Measurable f := (hφm.comp (measurable_fst.comp measurable_snd)).sub
    (hφm.comp (measurable_snd.comp measurable_snd))
  have he (a b : Fin 2) : Measurable (fun z : C(conditionalCorrectorBall R y, Mat 2) ×
      (FieldPair 2 × FieldPair 2) => conditionalCenteredSkew ζ R y σ z.2.1 a b -
        conditionalCenteredSkew ζ R y σ z.2.2 a b) := by
    have hm := ((continuous_apply b).comp (continuous_apply a)).measurable.comp hSm
    exact (hm.comp (measurable_fst.comp measurable_snd)).sub
      (hm.comp (measurable_snd.comp measurable_snd))
  have hgm : Measurable g := by
    unfold g frobeniusNorm frobeniusSq
    exact (Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ =>
      (he a b).mul (he a b)).sqrt
  have hdom : ∀ᵐ z ∂ν, |f z| + |g z| ≤ (C*R)*conditionalCopyGradientRms Q R y i z := by
    simpa only [ν, f, g, conditionalCopyGradientRms,
      frobeniusNorm, abs_of_nonneg (Real.sqrt_nonneg _)] using hb Q ζ R hR y i φ σ hφ hσ hc
  obtain ⟨hf, hg, hbound⟩ := paired_planar_joint_eLpNorm_le ν p f g
    (conditionalCopyGradientRms Q R y i) (by positivity : 0 ≤ C*R)
    hfm.aestronglyMeasurable hgm.aestronglyMeasurable hE hdom
  refine ⟨hφm, hSm, hf, hg, hbound.trans ?_⟩
  calc
    ENNReal.ofReal (2*(C*R)) * eLpNorm (conditionalCopyGradientRms Q R y i) p ν ≤
        ENNReal.ofReal (2*(C*R)) * ENNReal.ofReal (B/R) := mul_le_mul_right hEb _
    _ = ENNReal.ofReal ((2*C)*B) := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*(C*R))]
      congr 1
      field_simp
end EinsteinRelation.Correctors
