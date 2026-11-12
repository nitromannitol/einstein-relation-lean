import EinsteinRelation.Correctors.LocalMollifierDerivativeWeights

/-! # The full-space formulas for the local derivative corrections

Source: `paper/main.tex:921–938,942–963`. Restricting the center integral
to the mollifier's closed support preserves the literal scalar and matrix
corrections, without any assumption on the fields outside that support.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors
open EinsteinRelation.Entropy

attribute [local instance] MeasureTheory.Measure.Subtype.measureSpace

private theorem reflected_mollifier_gradient_eq_zero {d : ℕ} {R : ℝ}
    (hR : 0 < R) {y : Vec d} (hy : ¬ euclideanNorm y ≤ R) :
    gradient (Calculus.unitMassScaledMollifier d R) (-y) = 0 := by
  have hn : euclideanNorm (-y) = euclideanNorm y := by
    simp [euclideanNorm, euclideanSq, dot]
  funext j
  exact coordinateDerivative_unitMassScaledMollifier_eq_zero hR j
    (by rw [hn]; exact not_le.mp hy)

/-- The scalar correction on the center subtype is exactly the full-space
formula in the manuscript. Source: `paper/main.tex:921–938`. -/
theorem mollifier_scalar_derivative_integral_eq_centerIntegral {d : ℕ} {R : ℝ}
    (hR : 0 < R) (u : Vec d → ℝ) :
    (∫ y, u y • gradient (Calculus.unitMassScaledMollifier d R) (-y)) =
      ∫ y : {y : Vec d // euclideanNorm y ≤ R},
        u y.1 • gradient (Calculus.unitMassScaledMollifier d R) (-y.1) := by
  have hS : MeasurableSet {y : Vec d | euclideanNorm y ≤ R} :=
    (isClosed_le continuous_euclideanNorm' continuous_const).measurableSet
  calc
    _ = ∫ y in {y : Vec d | euclideanNorm y ≤ R},
        u y • gradient (Calculus.unitMassScaledMollifier d R) (-y) := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro y hy
      rw [reflected_mollifier_gradient_eq_zero hR hy, smul_zero]
    _ = _ := (integral_subtype hS (fun y => u y •
      gradient (Calculus.unitMassScaledMollifier d R) (-y))).symm

/-- The skew correction on the center subtype is exactly the full-space
matrix formula. Source: `paper/main.tex:921–938`. -/
theorem mollifier_skew_derivative_integral_eq_centerIntegral {d : ℕ} {R : ℝ}
    (hR : 0 < R) (S : Vec d → Mat d) :
    (∫ y, (S y).mulVec (gradient (Calculus.unitMassScaledMollifier d R) (-y))) =
      ∫ y : {y : Vec d // euclideanNorm y ≤ R},
        (S y.1).mulVec (gradient (Calculus.unitMassScaledMollifier d R) (-y.1)) := by
  have hS : MeasurableSet {y : Vec d | euclideanNorm y ≤ R} :=
    (isClosed_le continuous_euclideanNorm' continuous_const).measurableSet
  calc
    _ = ∫ y in {y : Vec d | euclideanNorm y ≤ R},
        (S y).mulVec (gradient (Calculus.unitMassScaledMollifier d R) (-y)) := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro y hy
      rw [reflected_mollifier_gradient_eq_zero hR hy, Matrix.mulVec_zero]
    _ = _ := (integral_subtype hS (fun y => (S y).mulVec
      (gradient (Calculus.unitMassScaledMollifier d R) (-y)))).symm

end EinsteinRelation.Correctors
