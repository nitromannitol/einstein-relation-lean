import EinsteinRelation.Correctors.CorrectorConditionalStatement
import EinsteinRelation.Correctors.SpatialBallTranslation
import EinsteinRelation.External.AKMLocalCorrectors

/-! # Recentered canonical gradient copies

Source: `paper/main.tex:817–875,886–894`. The pushforward of the actual
conditional copies has two stationary reduced marginals and coefficient
agreement on an origin ball. Point-gradient and spatial energy observables
are transported exactly; no equality with another conditional kernel is
required.
-/

open MeasureTheory
open scoped ENNReal

namespace EinsteinRelation.Correctors
open External.AKM
open NormalizedSpatialRepresentativeSupport

attribute [local instance] ReductionImageV3.fieldPair_standardBorel
local instance recenterRestrictionMeasurableSpace {d : ℕ} (U : Set (Vec d)) :
    MeasurableSpace C(U, Mat d) := borel C(U, Mat d)

/-- Translate both actual copies to place the observation center at zero.
Source: `paper/main.tex:817–875,886–894`. -/
noncomputable def recenteredConditionalCopyLaw {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (R : ℝ) (y : Point d) :
    Measure (FieldPair d × FieldPair d) :=
  (reducedConditionalCopyLaw (reducedEnvironmentLaw Q) (conditionalCorrectorBall R y)).map
    (fun z => (translate y.ofLp z.2.1, translate y.ofLp z.2.2))

/-- Both recentered copies have the original reduced marginal, and their
coefficients agree throughout the origin ball of radius `8R`.
Source: `paper/main.tex:817–875,886–894`. -/
theorem recenteredConditionalCopy_properties {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (R : ℝ) (y : Point d) :
    IsProbabilityMeasure (recenteredConditionalCopyLaw Q R y) ∧
      MeasurePreserving Prod.fst (recenteredConditionalCopyLaw Q R y)
        (reducedEnvironmentLaw Q) ∧
      MeasurePreserving Prod.snd (recenteredConditionalCopyLaw Q R y)
        (reducedEnvironmentLaw Q) ∧
      ∀ᵐ z ∂recenteredConditionalCopyLaw Q R y,
        Set.EqOn z.1.1 z.2.1 (originBall d (8*R)) := by
  let U := conditionalCorrectorBall R y
  let ν := reducedConditionalCopyLaw (reducedEnvironmentLaw Q) U
  let T : C(U, Mat d) × (FieldPair d × FieldPair d) → FieldPair d × FieldPair d :=
    fun z => (translate y.ofLp z.2.1, translate y.ofLp z.2.2)
  have hTm : Measurable T :=
    ((Probability.measurable_translate _).comp measurable_snd.fst).prodMk
      ((Probability.measurable_translate _).comp measurable_snd.snd)
  obtain ⟨hν, hfst, hsnd, heq⟩ := reducedConditionalCopy_properties
    (reducedEnvironmentLaw Q) U (isOpen_conditionalCorrectorBall R y)
  change ν.map (fun z => z.2.1) = reducedEnvironmentLaw Q at hfst
  change ν.map (fun z => z.2.2) = reducedEnvironmentLaw Q at hsnd
  letI : IsProbabilityMeasure ν := hν
  have hshift := measurePreserving_translate (reducedEnvironmentLaw Q)
    (reducedEnvironmentLaw_stationary Q) y.ofLp
  refine ⟨Measure.isProbabilityMeasure_map hTm.aemeasurable, ⟨measurable_fst, ?_⟩,
    ⟨measurable_snd, ?_⟩, ?_⟩
  · change (ν.map T).map Prod.fst = _
    rw [Measure.map_map measurable_fst hTm]
    change ν.map (translate y.ofLp ∘ (fun z => z.2.1)) = _
    rw [← Measure.map_map (Probability.measurable_translate _) measurable_snd.fst,
      hfst, hshift.map_eq]
  · change (ν.map T).map Prod.snd = _
    rw [Measure.map_map measurable_snd hTm]
    change ν.map (translate y.ofLp ∘ (fun z => z.2.2)) = _
    rw [← Measure.map_map (Probability.measurable_translate _) measurable_snd.snd,
      hsnd, hshift.map_eq]
  · change ∀ᵐ z ∂ν.map T, Set.EqOn z.1.1 z.2.1 (originBall d (8*R))
    letI : PolishSpace (CoefficientField d) := Localization.coefficientField_polish d
    have hm : MeasurableSet {z : FieldPair d × FieldPair d |
        Set.EqOn z.1.1 z.2.1 (originBall d (8*R))} := by
      have hclosed : IsClosed {z : FieldPair d × FieldPair d |
          ∀ x ∈ originBall d (8*R), z.1.1 x = z.2.1 x} :=
        by
          simp only [Set.setOf_forall]
          exact isClosed_iInter fun x => isClosed_iInter fun _ =>
            isClosed_eq ((continuous_eval_const x).comp continuous_fst.fst)
              ((continuous_eval_const x).comp continuous_snd.fst)
      exact hclosed.measurableSet
    apply (ae_map_iff hTm.aemeasurable hm).mpr
    filter_upwards [heq] with z hz
    intro x hx
    apply hz
    change dist (WithLp.toLp 2 (y.ofLp + x)) y < 8*R
    rw [dist_eq_norm]
    have hsub : (WithLp.toLp 2 (y.ofLp + x) : Point d) - y = WithLp.toLp 2 x := by
      apply WithLp.ofLp_injective
      simp
    rw [hsub]
    simpa only [originBall, Set.mem_setOf_eq,
      TimeChange.euclideanNorm_eq_norm_toLp] using hx

/-- The prescribed canonical point-gradient seminorm is precisely the
origin seminorm on the recentered coupling.
Source: `paper/main.tex:861–875,886–894`. -/
theorem eLpNorm_conditionalCorrectorGradient_eq_recentered {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (R : ℝ) (y : Point d) (i : Fin d) (p : ℝ≥0∞) :
    eLpNorm (fun z : C(conditionalCorrectorBall R y, Mat d) ×
      (FieldPair d × FieldPair d) => euclideanNorm
        (conditionalCorrectorGradient Q i y z.2.1 - conditionalCorrectorGradient Q i y z.2.2))
      p (reducedConditionalCopyLaw (reducedEnvironmentLaw Q) (conditionalCorrectorBall R y)) =
    eLpNorm (fun z : FieldPair d × FieldPair d => euclideanNorm
      (conditionalCorrectorGradient Q i 0 z.1 - conditionalCorrectorGradient Q i 0 z.2))
      p (recenteredConditionalCopyLaw Q R y) := by
  let T : C(conditionalCorrectorBall R y, Mat d) ×
      (FieldPair d × FieldPair d) → FieldPair d × FieldPair d :=
    fun z => (translate y.ofLp z.2.1, translate y.ofLp z.2.2)
  have hTm : Measurable T :=
    ((Probability.measurable_translate _).comp measurable_snd.fst).prodMk
      ((Probability.measurable_translate _).comp measurable_snd.snd)
  have hgrad : Measurable (conditionalCorrectorGradient Q i 0) :=
    (PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin d => ℝ)).measurable.comp
      ((Lp.stronglyMeasurable (canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))).measurable.comp
          (Probability.measurable_translate 0))
  have hnorm : Measurable (fun z : FieldPair d × FieldPair d => euclideanNorm
      (conditionalCorrectorGradient Q i 0 z.1 - conditionalCorrectorGradient Q i 0 z.2)) := by
    unfold euclideanNorm euclideanSq dot
    fun_prop
  have he := eLpNorm_map_measure
    (μ := reducedConditionalCopyLaw (reducedEnvironmentLaw Q) (conditionalCorrectorBall R y))
    hnorm.aestronglyMeasurable hTm.aemeasurable (p := p)
  simpa only [recenteredConditionalCopyLaw, Function.comp_def, T,
    conditionalCorrectorGradient, StationarySpatialRealization.spatialRealization,
    WithLp.ofLp_zero, translate_zero] using he.symm

end EinsteinRelation.Correctors
