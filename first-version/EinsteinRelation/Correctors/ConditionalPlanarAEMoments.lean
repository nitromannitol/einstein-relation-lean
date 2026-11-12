import EinsteinRelation.Correctors.ConditionalCopyPlanarMoments
import EinsteinRelation.Correctors.ConditionalCopyAEJensen

/-! Source: `paper/main.tex:872-894`. The planar copy comparison only
needs almost-everywhere measurability of the centered skew observable;
joint measurability of the supplied continuous representative is unnecessary. -/

open MeasureTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors
open External.GilbargTrudinger NormalizedSpatialRepresentativeSupport HeatSelectedSkewMeaning
open NormalizedScalarPhysicalLawTransportSupport

attribute [local instance] ReductionImageV3.fieldPair_standardBorel
local instance planarFact : Fact (2 ≤ 2) := ⟨by decide⟩
local instance planarRestrictionMeasurableSpace {d : ℕ} (U : Set (Vec d)) :
    MeasurableSpace C(U, Mat d) := borel C(U, Mat d)

/-- Planar spatial energy controls both centered copy moments for the
actual continuous representatives. Source: `paper/main.tex:872-894`. -/
theorem paired_planar_centered_moments_of_energy_ae
    (h817 : LocalBoundednessEstimate) (hP : BallPoincareEstimate) (L : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {r₀ : ℝ} (Q : EnvironmentLaw 2 L r₀)
      (ζ : SourceMollifier 2) (R : ℝ) (hR : 1 ≤ R) (y : Point 2) (i : Fin 2)
      (φ : FieldPair 2 → Point 2 → ℝ) (σ : FieldPair 2 → Vec 2 → Mat 2),
      IsNormalizedCanonicalScalarCorrector Q i ζ R hR y φ →
      HasHeatSelectedSkewCorrectorColumn (by decide) Q i σ →
      (∀ᵐ ω ∂reducedEnvironmentLaw Q, Continuous (φ ω) ∧ Continuous (σ ω)) →
      AEStronglyMeasurable (conditionalCenteredSkew ζ R y σ) (reducedEnvironmentLaw Q) →
      ∀ (p : ℝ≥0∞) (B : ℝ), 0 ≤ B →
      MemLp (conditionalCopyGradientRms Q R y i) p
        (reducedConditionalCopyLaw (reducedEnvironmentLaw Q) (conditionalCorrectorBall R y)) →
      eLpNorm (conditionalCopyGradientRms Q R y i) p
        (reducedConditionalCopyLaw (reducedEnvironmentLaw Q) (conditionalCorrectorBall R y)) ≤
          ENNReal.ofReal (B/R) →
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
  intro r₀ Q ζ R hR y i φ σ hφ hσ hc hSm p B hB hE hEb
  have hφm := (measurable_conditionalCentered_of_joint ζ R y φ
    (fun _ _ => 0) hφ.1 (fun _ _ => measurable_const)).1
  let ν := reducedConditionalCopyLaw (reducedEnvironmentLaw Q) (conditionalCorrectorBall R y)
  let f := fun z : C(conditionalCorrectorBall R y, Mat 2) × (FieldPair 2 × FieldPair 2) =>
    conditionalCenteredScalar ζ R y φ z.2.1 - conditionalCenteredScalar ζ R y φ z.2.2
  let g := fun z : C(conditionalCorrectorBall R y, Mat 2) × (FieldPair 2 × FieldPair 2) =>
    frobeniusNorm (conditionalCenteredSkew ζ R y σ z.2.1 -
      conditionalCenteredSkew ζ R y σ z.2.2)
  obtain ⟨_, hfirst, hsecond, _⟩ := reducedConditionalCopy_properties
    (reducedEnvironmentLaw Q) (conditionalCorrectorBall R y) (isOpen_conditionalCorrectorBall R y)
  have hmp₁ : MeasurePreserving
      (fun z : C(conditionalCorrectorBall R y, Mat 2) × (FieldPair 2 × FieldPair 2) => z.2.1)
      ν (reducedEnvironmentLaw Q) := ⟨measurable_snd.fst, hfirst⟩
  have hmp₂ : MeasurePreserving
      (fun z : C(conditionalCorrectorBall R y, Mat 2) × (FieldPair 2 × FieldPair 2) => z.2.2)
      ν (reducedEnvironmentLaw Q) := ⟨measurable_snd.snd, hsecond⟩
  have hfm : AEStronglyMeasurable f ν :=
    (hφm.aestronglyMeasurable.comp_quasiMeasurePreserving hmp₁.quasiMeasurePreserving).sub
      (hφm.aestronglyMeasurable.comp_quasiMeasurePreserving hmp₂.quasiMeasurePreserving)
  have hdiff := (hSm.comp_quasiMeasurePreserving hmp₁.quasiMeasurePreserving).sub
    (hSm.comp_quasiMeasurePreserving hmp₂.quasiMeasurePreserving)
  have hnorm : Continuous (fun A : Mat 2 => frobeniusNorm A) := by
    unfold frobeniusNorm frobeniusSq
    fun_prop
  have hgm : AEStronglyMeasurable g ν := hnorm.comp_aestronglyMeasurable hdiff
  have hdom : ∀ᵐ z ∂ν, |f z| + |g z| ≤ (C*R)*conditionalCopyGradientRms Q R y i z := by
    simpa only [ν, f, g, conditionalCopyGradientRms,
      frobeniusNorm, abs_of_nonneg (Real.sqrt_nonneg _)] using hb Q ζ R hR y i φ σ hφ hσ hc
  obtain ⟨hf, hg, hbound⟩ := paired_planar_joint_eLpNorm_le ν p f g
    (conditionalCopyGradientRms Q R y i) (by positivity : 0 ≤ C*R)
    hfm hgm hE hdom
  refine ⟨hf, hg, hbound.trans ?_⟩
  calc
    ENNReal.ofReal (2*(C*R)) * eLpNorm (conditionalCopyGradientRms Q R y i) p ν ≤
        ENNReal.ofReal (2*(C*R)) * ENNReal.ofReal (B/R) := mul_le_mul_right hEb _
    _ = ENNReal.ofReal ((2*C)*B) := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*(C*R))]
      congr 1
      have : R ≠ 0 := ne_of_gt (zero_lt_one.trans_le hR)
      field_simp

end EinsteinRelation.Correctors
