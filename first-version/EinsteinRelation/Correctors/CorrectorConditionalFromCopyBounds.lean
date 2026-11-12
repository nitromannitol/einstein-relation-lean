import EinsteinRelation.Correctors.CorrectorConditionalStatement
import EinsteinRelation.Correctors.ConditionalCopyFrobeniusJensen

/-! # Lemma 5.2 assembly from paired estimates

Source: `paper/main.tex:853–886`. The remaining inputs below are internal
paired-corrector estimates. They are explicit hypotheses, not literature
inputs. The canonical-gradient integrability and the conditional-copy
construction are already proved on the actual reduced law.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace EinsteinRelation.Correctors
open NormalizedSpatialRepresentativeSupport
open NormalizedScalarPhysicalLawTransportSupport HeatSelectedSkewMeaning

attribute [local instance] ReductionImageV3.fieldPair_standardBorel
local instance assemblyRestrictionMeasurableSpace {d : ℕ} (U : Set (Vec d)) :
    MeasurableSpace C(U, Mat d) := borel C(U, Mat d)

/-- Tensor copy Jensen on the actual production observation sigma algebra.
Source: `paper/main.tex:878–886`. -/
theorem eLpNorm_reduced_conditional_frobenius_le_copy_difference {d : ℕ}
    (μ : Measure (FieldPair d)) [IsProbabilityMeasure μ]
    (U : Set (Vec d)) (hU : IsOpen U) {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    {f : FieldPair d → Mat d} (hfm : Measurable f)
    (hfi : ∀ a b, Integrable (fun ω => f ω a b) μ) :
    eLpNorm (fun ω => frobeniusNorm (Matrix.of (fun a b => f ω a b -
      condExp (Carriers.reducedCoefficientObservationSigma U) μ
        (fun ω' => f ω' a b) ω))) p μ ≤
      eLpNorm (fun z : C(U, Mat d) × (FieldPair d × FieldPair d) =>
        frobeniusNorm (f z.2.1 - f z.2.2)) p (reducedConditionalCopyLaw μ U) := by
  rw [reducedCoefficientObservationSigma_eq_comap_restriction U hU]
  exact eLpNorm_conditional_error_frobenius_le_copy_difference μ
    (reducedCoefficientRestriction U) (measurable_reducedCoefficientRestriction U)
    hp hpt hfm hfi

/-- The exact conditional conclusions at a prescribed scale follow from
the actual conditional-copy estimates. All unproved analytic requirements
are visible: the paired point-gradient bound and, in dimension two, the
centered scalar/tensor bounds and their integrability.
Source: `paper/main.tex:853–886`. -/
theorem correctorConditional_at_scale_of_copy_bounds
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (ζ : SourceMollifier d)
    (R : ℝ) (y : Point d) (i : Fin d)
    (φ : FieldPair d → Point d → ℝ) (σ : FieldPair d → Vec d → Mat d)
    {m C : ℝ} (hm : 1 ≤ m)
    (hgradient :
      eLpNorm (fun z : C(conditionalCorrectorBall R y, Mat d) × (FieldPair d × FieldPair d) =>
        euclideanNorm (conditionalCorrectorGradient Q i y z.2.1 -
          conditionalCorrectorGradient Q i y z.2.2)) (ENNReal.ofReal m)
        (reducedConditionalCopyLaw (reducedEnvironmentLaw Q) (conditionalCorrectorBall R y)) ≤
          ENNReal.ofReal (C * R ^ (-(d : ℝ) / 2)))
    (hcentered : d = 2 →
      Measurable (conditionalCenteredScalar ζ R y φ) ∧
      Integrable (conditionalCenteredScalar ζ R y φ) (reducedEnvironmentLaw Q) ∧
      Measurable (conditionalCenteredSkew ζ R y σ) ∧
      (∀ a b, Integrable (fun ω => conditionalCenteredSkew ζ R y σ ω a b)
        (reducedEnvironmentLaw Q)) ∧
      eLpNorm (fun z : C(conditionalCorrectorBall R y, Mat d) × (FieldPair d × FieldPair d) =>
        conditionalCenteredScalar ζ R y φ z.2.1 - conditionalCenteredScalar ζ R y φ z.2.2)
        (ENNReal.ofReal m)
        (reducedConditionalCopyLaw (reducedEnvironmentLaw Q) (conditionalCorrectorBall R y)) +
      eLpNorm (fun z : C(conditionalCorrectorBall R y, Mat d) × (FieldPair d × FieldPair d) =>
        frobeniusNorm (conditionalCenteredSkew ζ R y σ z.2.1 -
          conditionalCenteredSkew ζ R y σ z.2.2)) (ENNReal.ofReal m)
        (reducedConditionalCopyLaw (reducedEnvironmentLaw Q) (conditionalCorrectorBall R y)) ≤
          ENNReal.ofReal C) :
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
          (ENNReal.ofReal m) μ ≤ ENNReal.ofReal C) := by
  dsimp only
  have hU := isOpen_conditionalCorrectorBall R y
  have hp := ENNReal.one_le_ofReal.mpr hm
  refine ⟨?_, ?_⟩
  · exact (eLpNorm_canonicalGradient_euclidean_conditional_error_le_copy_difference Q i
      (WithLp.ofLp y) (conditionalCorrectorBall R y) hU hp ENNReal.ofReal_ne_top).trans hgradient
  · intro hd
    obtain ⟨hsm, hsi, htm, hti, hb⟩ := hcentered hd
    exact (add_le_add
      (eLpNorm_reduced_conditional_error_le_copy_difference (reducedEnvironmentLaw Q)
        (conditionalCorrectorBall R y) hU hp ENNReal.ofReal_ne_top hsm hsi)
      (eLpNorm_reduced_conditional_frobenius_le_copy_difference (reducedEnvironmentLaw Q)
        (conditionalCorrectorBall R y) hU hp ENNReal.ofReal_ne_top htm hti)).trans hb

/-- A complete production-carrier implication for Lemma 5.2. The uniform
paired estimates of Steps 2–3, including the centered observables' moment
requirements, remain explicit internal proof obligations. The constant is
chosen before the environment law. Source: `paper/main.tex:766–886`. -/
theorem correctorConditional_of_uniform_copy_bounds
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
              ENNReal.ofReal C)) :
    CorrectorConditionalStatement := by
  intro d hd Λ₀ r₀ ζ m hm
  obtain ⟨C, hC⟩ := hcopies d Λ₀ r₀ ζ m hm
  refine ⟨C, ?_⟩
  intro Q R hR y i φ σ hφ hσ
  obtain ⟨hgradient, hcentered⟩ := hC Q R hR y i φ σ hφ hσ
  exact correctorConditional_at_scale_of_copy_bounds Q ζ R y i φ σ
    (by linarith : 1 ≤ m) hgradient hcentered

end EinsteinRelation.Correctors
