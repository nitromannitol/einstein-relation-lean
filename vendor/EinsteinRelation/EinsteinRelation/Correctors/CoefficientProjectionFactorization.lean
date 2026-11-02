import EinsteinRelation.Correctors.CoefficientConditionalProjection
import Mathlib.MeasureTheory.Function.FactorsThrough

/-!
# Genuine coefficient factors of the conditional projection

Source: `paper/main.tex:693-698`. The conditional projection admits a
strongly measurable factor on continuous coefficients alone. Equality is
of actual L² representatives almost everywhere; no clock component is
included in the factor's domain.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

/-- A projected stationary field has a strongly measurable representative
which depends on the continuous coefficient field alone. -/
theorem exists_coefficient_factor_of_projection {d : ℕ}
    (Q : Measure (FieldPair d)) {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (G : Lp E 2 Q) :
    ∃ F : CoefficientField d → E, StronglyMeasurable F ∧
      (coefficientProjection Q E G : FieldPair d → E) =ᵐ[Q] fun ω => F ω.1 := by
  have h := coefficientProjection_aestronglyMeasurable Q G
  obtain ⟨F, hF, hfact⟩ := h.stronglyMeasurable_mk.exists_eq_measurable_comp
  refine ⟨F, hF, ?_⟩
  filter_upwards [h.ae_eq_mk] with ω hω
  exact hω.trans (congrFun hfact ω)

end EinsteinRelation.Correctors
