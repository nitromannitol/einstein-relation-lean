import EinsteinRelation.Correctors.CanonicalVariationalGradientSupport
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2

/-!
# Conditional projection onto coefficient observations

Source: `paper/main.tex:693-698`. The reduced environment contains both a
coefficient and a clock. This projection retains precisely the Borel
observations of the continuous coefficient field. Its range does not retain
the clock. Transport to AKM's test-integral carrier is a separate step.
-/

open MeasureTheory

noncomputable section

namespace EinsteinRelation.Correctors

/-- Borel observations of the continuous coefficient component alone. -/
def coefficientObservations (d : ℕ) : MeasurableSpace (FieldPair d) :=
  MeasurableSpace.comap (Prod.fst : FieldPair d → CoefficientField d) inferInstance

theorem coefficientObservations_le (d : ℕ) :
    coefficientObservations d ≤ (inferInstance : MeasurableSpace (FieldPair d)) :=
  (continuous_fst : Continuous (Prod.fst : FieldPair d → CoefficientField d)).measurable.comap_le

/-- Orthogonal L² projection which discards the clock observations. -/
def coefficientProjection {d : ℕ} (Q : Measure (FieldPair d))
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    Lp E 2 Q →L[ℝ] Lp E 2 Q :=
  (lpMeas E ℝ (coefficientObservations d) 2 Q).subtypeL.comp
    (condExpL2 E ℝ (μ := Q) (m := coefficientObservations d) (coefficientObservations_le d))

/-- The projected class has a coefficient-measurable representative. -/
theorem coefficientProjection_aestronglyMeasurable {d : ℕ} (Q : Measure (FieldPair d))
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : Lp E 2 Q) :
    AEStronglyMeasurable[coefficientObservations d] (coefficientProjection Q E f) Q :=
  aestronglyMeasurable_condExpL2 (coefficientObservations_le d) f

/-- Discarding the clock is a contraction in the actual L² norm. -/
theorem norm_coefficientProjection_le {d : ℕ} (Q : Measure (FieldPair d))
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : Lp E 2 Q) : ‖coefficientProjection Q E f‖ ≤ ‖f‖ :=
  norm_condExpL2_coe_le (coefficientObservations_le d) f

/-- The coefficient projection is self-adjoint. -/
theorem inner_coefficientProjection_left_eq_right {d : ℕ}
    (Q : Measure (FieldPair d)) {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f g : Lp E 2 Q) :
    inner ℝ (coefficientProjection Q E f) g =
      inner ℝ f (coefficientProjection Q E g) :=
  inner_condExpL2_left_eq_right (coefficientObservations_le d)

/-- Coefficient-measurable classes are fixed by this projection. -/
theorem coefficientProjection_eq_self {d : ℕ} (Q : Measure (FieldPair d))
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : Lp E 2 Q) (hf : AEStronglyMeasurable[coefficientObservations d] f Q) :
    coefficientProjection Q E f = f := by
  letI : Fact (coefficientObservations d ≤
      (inferInstance : MeasurableSpace (FieldPair d))) := ⟨coefficientObservations_le d⟩
  change (lpMeas E ℝ (coefficientObservations d) 2 Q).starProjection f = f
  exact Submodule.starProjection_eq_self_iff.mpr
    (mem_lpMeas_iff_aestronglyMeasurable.mpr hf)

end EinsteinRelation.Correctors
