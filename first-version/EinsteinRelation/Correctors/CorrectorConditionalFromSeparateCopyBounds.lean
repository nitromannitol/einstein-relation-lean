import EinsteinRelation.Correctors.CorrectorConditionalFromCopyBounds

/-! # Separate gradient and planar copy obligations for Lemma 5.2

Source: `paper/main.tex:861–894`. The gradient estimate is independent of
the chosen potentials. The centered planar estimate retains their exact
normalization. Combining the independently uniform constants preserves
quantification before the law, scale, center and coordinate.
-/

open MeasureTheory ProbabilityTheory
namespace EinsteinRelation.Correctors
open NormalizedSpatialRepresentativeSupport
open NormalizedScalarPhysicalLawTransportSupport HeatSelectedSkewMeaning
attribute [local instance] ReductionImageV3.fieldPair_standardBorel
local instance separateRestrictionMeasurableSpace {d : ℕ} (U : Set (Vec d)) :
    MeasurableSpace C(U, Mat d) := borel C(U, Mat d)

/-- Independent paired gradient and centered planar bounds suffice, with
all measurability and integrability requirements visible.
Source: `paper/main.tex:861–894`. -/
theorem correctorConditional_of_separate_copy_bounds
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
              ENNReal.ofReal C)) :
    CorrectorConditionalStatement := by
  apply correctorConditional_of_uniform_copy_bounds
  intro d _ Λ₀ r₀ ζ m hm
  obtain ⟨Cg, hg⟩ := hgradient d Λ₀ r₀ m hm
  obtain ⟨Cp, hc⟩ := hplanar d Λ₀ r₀ ζ m hm
  refine ⟨max Cg Cp, ?_⟩
  intro Q R hR y i φ σ hφ hσ
  refine ⟨(hg Q R hR y i).trans ?_, ?_⟩
  · exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (le_max_left _ _) (Real.rpow_nonneg (zero_lt_one.trans_le hR).le _))
  · intro hd
    obtain ⟨hsm, hsi, htm, hti, hb⟩ := hc Q R hR y i φ σ hφ hσ hd
    exact ⟨hsm, hsi, htm, hti,
      hb.trans (ENNReal.ofReal_le_ofReal (le_max_right _ _))⟩

end EinsteinRelation.Correctors
