import EinsteinRelation.Correctors.CoefficientConditionalProjection

/-!
# Symmetric actions commuting with the coefficient projection

Source: `paper/main.tex:693-698`. An invariant coefficient-measurable
subspace is reducing for a symmetric action, so its orthogonal projection
commutes with that action.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors

/-- The orthogonal coefficient projection commutes with every symmetric
continuous linear action preserving coefficient-measurable classes. -/
theorem coefficientProjection_commutes_of_symmetric
    {d : ℕ} (Q : Measure (FieldPair d)) {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : Lp E 2 Q →L[ℝ] Lp E 2 Q)
    (hA : ∀ u v, inner ℝ u (A v) = inner ℝ (A u) v)
    (hpres : ∀ f : Lp E 2 Q,
      AEStronglyMeasurable[coefficientObservations d] f Q →
      AEStronglyMeasurable[coefficientObservations d] (A f) Q)
    (f : Lp E 2 Q) :
    coefficientProjection Q E (A f) = A (coefficientProjection Q E f) := by
  let P := coefficientProjection Q E
  have hfix (g : Lp E 2 Q) : P (A (P g)) = A (P g) :=
    coefficientProjection_eq_self Q _
      (hpres _ (coefficientProjection_aestronglyMeasurable Q g))
  apply ext_inner_right ℝ
  intro g
  calc
    inner ℝ (P (A f)) g = inner ℝ (A f) (P g) :=
      inner_coefficientProjection_left_eq_right Q _ _
    _ = inner ℝ f (A (P g)) := (hA f (P g)).symm
    _ = inner ℝ f (P (A (P g))) := by rw [hfix]
    _ = inner ℝ (P f) (A (P g)) :=
      (inner_coefficientProjection_left_eq_right Q _ _).symm
    _ = inner ℝ (A (P f)) (P g) := hA _ _
    _ = inner ℝ (P (A (P f))) g :=
      (inner_coefficientProjection_left_eq_right Q _ _).symm
    _ = inner ℝ (A (P f)) g := by rw [hfix]

end EinsteinRelation.Correctors
