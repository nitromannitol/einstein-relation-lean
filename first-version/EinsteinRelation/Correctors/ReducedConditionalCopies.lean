import EinsteinRelation.Correctors.ConditionalCopyProperties
import EinsteinRelation.Correctors.ConditionalCopyJensen
import EinsteinRelation.Carriers.RegenerationCorrectorTwins
import EinsteinRelation.Environment.ReductionImageSupport
import EinsteinRelation.Localization.CoefficientObservations

/-! # Conditional copies on the production reduced-environment carrier

Source: `paper/main.tex:765–767,886–894`. The observation of a reduced
environment is the restriction of its first coordinate. The conditional
copies have the original full environment law as both marginals, while
their coefficient fields agree throughout the observed open set. This
allows measurable corrector observables to be compared on the actual
production carrier.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open EinsteinRelation.Carriers (reducedCoefficientObservationSigma)

namespace EinsteinRelation.Correctors

attribute [local instance] ReductionImageV3.fieldPair_standardBorel

/-- The compact-open restriction of the coefficient already stored in a
reduced environment. Source: `paper/main.tex:765–767,886–894`. -/
def reducedCoefficientRestriction {d : ℕ} (U : Set (Vec d))
    (ω : FieldPair d) : C(U, Mat d) := ω.1.restrict U

/-- The production coefficient sigma algebra is the pullback of the
standard Borel restriction observation. Source: `paper/main.tex:765–767`. -/
theorem reducedCoefficientObservationSigma_eq_comap_restriction {d : ℕ}
    (U : Set (Vec d)) (hU : IsOpen U) :
    reducedCoefficientObservationSigma U =
      (borel C(U, Mat d)).comap (reducedCoefficientRestriction U) := by
  rw [Localization.borel_restriction_eq_evaluationSigma U hU,
    MeasurableSpace.comap_iSup]
  apply iSup_congr
  intro x
  rw [MeasurableSpace.comap_comp]
  rfl

/-- The literal coefficient restriction is measurable on the full
production environment carrier. Source: `paper/main.tex:886–894`. -/
theorem measurable_reducedCoefficientRestriction {d : ℕ} (U : Set (Vec d)) :
    @Measurable (FieldPair d) C(U, Mat d) inferInstance (borel C(U, Mat d))
      (reducedCoefficientRestriction U) :=
  ((ContinuousMap.continuous_restrict U).comp continuous_fst).borel_measurable

/-- The actual conditional product of reduced-environment copies has
both original marginals and coefficient agreement at every observed point.
The observables may be measurable functions of the full environment.
Source: `paper/main.tex:886–894`. -/
theorem reducedConditionalCopy_properties {d : ℕ}
    (μ : Measure (FieldPair d)) [IsProbabilityMeasure μ]
    (U : Set (Vec d)) (hU : IsOpen U) :
    letI : MeasurableSpace C(U, Mat d) := borel C(U, Mat d)
    let X := reducedCoefficientRestriction U
    let P := (μ.map X) ⊗ₘ
      (condDistrib (id : FieldPair d → FieldPair d) X μ ×ₖ
        condDistrib (id : FieldPair d → FieldPair d) X μ)
    IsProbabilityMeasure P ∧
      P.map (fun z : C(U, Mat d) × (FieldPair d × FieldPair d) => z.2.1) = μ ∧
      P.map (fun z : C(U, Mat d) × (FieldPair d × FieldPair d) => z.2.2) = μ ∧
      ∀ᵐ z ∂P, Set.EqOn z.2.1.1 z.2.2.1 U := by
  letI : MeasurableSpace C(U, Mat d) := borel C(U, Mat d)
  letI : StandardBorelSpace C(U, Mat d) :=
    Localization.coefficientRestriction_standardBorel U hU
  obtain ⟨hp, hfirst, hsecond, hagree⟩ :=
    conditionalCopy_properties μ (reducedCoefficientRestriction U)
      (measurable_reducedCoefficientRestriction U)
  refine ⟨hp, hfirst, hsecond, ?_⟩
  filter_upwards [hagree] with z hz
  intro x hx
  exact DFunLike.congr_fun hz (⟨x, hx⟩ : U)

/-- Conditional-copy Jensen for the exact production coefficient sigma
algebra. The scalar observable may be centered before applying this lemma.
Source: `paper/main.tex:886–894`. -/
theorem eLpNorm_reduced_conditional_error_le_copy_difference {d : ℕ}
    (μ : Measure (FieldPair d)) [IsProbabilityMeasure μ]
    (U : Set (Vec d)) (hU : IsOpen U) {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    {f : FieldPair d → ℝ} (hfm : Measurable f) (hfi : Integrable f μ) :
    letI : MeasurableSpace C(U, Mat d) := borel C(U, Mat d)
    let X := reducedCoefficientRestriction U
    eLpNorm (f - μ[f | reducedCoefficientObservationSigma U]) p μ ≤
      eLpNorm (fun z : C(U, Mat d) × (FieldPair d × FieldPair d) =>
        f z.2.1 - f z.2.2) p
        ((μ.map X) ⊗ₘ (condDistrib (id : FieldPair d → FieldPair d) X μ ×ₖ
          condDistrib (id : FieldPair d → FieldPair d) X μ)) := by
  letI : MeasurableSpace C(U, Mat d) := borel C(U, Mat d)
  dsimp only
  rw [reducedCoefficientObservationSigma_eq_comap_restriction U hU]
  exact eLpNorm_conditional_error_le_copy_difference μ
    (reducedCoefficientRestriction U) (measurable_reducedCoefficientRestriction U)
    hp hpt hfm hfi

end EinsteinRelation.Correctors
