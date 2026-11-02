import EinsteinRelation.Correctors.CoefficientConditionalProjection
import EinsteinRelation.Calculus.HorizontalTranslationLp

/-!
# Translation invariance of the coefficient projection

Source: `paper/main.tex:693-698`. Translation preserves the coefficient-only
observations. Both the action and its inverse preserve the corresponding
L² subspace, so its orthogonal projection commutes with translation.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors

/-- Translating both fields preserves the coefficient-only sigma algebra. -/
theorem measurable_translate_coefficientObservations {d : ℕ} (x : Vec d) :
    Measurable[coefficientObservations d, coefficientObservations d] (translate x) := by
  let T : CoefficientField d → CoefficientField d := fun a => (translate x (a, 0)).1
  have hT : Continuous T := continuous_fst.comp
    (Probability.continuous_translate.comp
      (continuous_const.prodMk (continuous_id.prodMk continuous_const)))
  apply measurable_comap_iff.mpr
  exact hT.measurable.comp (comap_measurable Prod.fst)

/-- The actual L² translation preserves coefficient-measurable classes. -/
theorem translationLp_aestronglyMeasurable_coefficients {d : ℕ}
    (Q : Measure (FieldPair d)) (hQ : IsStationary Q) (x : Vec d) (f : Lp ℝ 2 Q)
    (hf : AEStronglyMeasurable[coefficientObservations d] f Q) :
    AEStronglyMeasurable[coefficientObservations d] (translationLp Q hQ x f) Q := by
  have h := hf.stronglyMeasurable_mk.comp_measurable (measurable_translate_coefficientObservations x)
  apply h.aestronglyMeasurable.congr
  filter_upwards [(measurePreserving_translate Q hQ x).quasiMeasurePreserving.ae hf.ae_eq_mk,
    coeFn_translationLp Q hQ x f] with ω hω hT
  exact hω.symm.trans hT.symm

private theorem inner_translation_adjoint {d : ℕ} (Q : Measure (FieldPair d))
    (hQ : IsStationary Q) (x : Vec d) (f g : Lp ℝ 2 Q) :
    inner ℝ (translationLp Q hQ x f) g = inner ℝ f (translationLp Q hQ (-x) g) := by
  have h := (translationLp Q hQ x).inner_map_map f (translationLp Q hQ (-x) g)
  rw [← translationLp_add, add_neg_cancel, translationLp_zero] at h
  exact h

/-- The actual coefficient-only projection commutes with spatial translation. -/
theorem coefficientProjection_translationLp {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (x : Vec d) (f : Lp ℝ 2 Q) :
    coefficientProjection Q ℝ (translationLp Q hQ x f) =
      translationLp Q hQ x (coefficientProjection Q ℝ f) := by
  let P := coefficientProjection Q ℝ
  let U := translationLp Q hQ
  have hfix (y : Vec d) (g : Lp ℝ 2 Q) : P (U y (P g)) = U y (P g) :=
    coefficientProjection_eq_self Q _
      (translationLp_aestronglyMeasurable_coefficients Q hQ y _
        (coefficientProjection_aestronglyMeasurable Q g))
  apply ext_inner_right ℝ
  intro g
  calc
    inner ℝ (P (U x f)) g = inner ℝ (U x f) (P g) :=
      inner_coefficientProjection_left_eq_right Q _ _
    _ = inner ℝ f (U (-x) (P g)) := inner_translation_adjoint Q hQ _ _ _
    _ = inner ℝ f (P (U (-x) (P g))) := by rw [hfix]
    _ = inner ℝ (P f) (U (-x) (P g)) :=
      (inner_coefficientProjection_left_eq_right Q _ _).symm
    _ = inner ℝ (U x (P f)) (P g) := (inner_translation_adjoint Q hQ _ _ _).symm
    _ = inner ℝ (P (U x (P f))) g :=
      (inner_coefficientProjection_left_eq_right Q _ _).symm
    _ = inner ℝ (U x (P f)) g := by rw [hfix]

end EinsteinRelation.Correctors
