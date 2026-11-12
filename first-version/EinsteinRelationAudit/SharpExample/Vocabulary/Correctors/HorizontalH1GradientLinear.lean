import EinsteinRelationAudit.SharpExample.Vocabulary.Calculus.HorizontalSobolev

/-! Restated from the library module `EinsteinRelation.Correctors.HorizontalH1GradientLinear`:
the declarations of that module that the statement of
`EinsteinRelationAudit.SharpExample.mobility_rate_sharp` depends on, in their module context. -/

open MeasureTheory
namespace EinsteinRelation
/-- Source main.tex240–248: the chosen horizontal gradient is additive on the generator domain. -/
theorem horizontalH1Gradient_add {d : ℕ} (Q : Measure (FieldPair d)) (hQ : IsStationary Q)
    (f g : horizontalH1 Q hQ) (i : Fin d) :
    horizontalH1Gradient Q hQ (f + g) i =
      horizontalH1Gradient Q hQ f i + horizontalH1Gradient Q hQ g i := by
  have hadd : ∀ j : Fin d, HasHorizontalLpDerivative Q hQ j ((f + g : horizontalH1 Q hQ) : Lp ℝ 2 Q)
      (horizontalH1Gradient Q hQ f j + horizontalH1Gradient Q hQ g j) := fun j => by
    rw [Submodule.coe_add]
    exact (hasHorizontalLpDerivative_horizontalH1Gradient Q hQ f j).add
      (hasHorizontalLpDerivative_horizontalH1Gradient Q hQ g j)
  exact congrFun (horizontalH1Gradient_eq_of_hasHorizontalLpDerivative Q hQ (f + g)
    (fun j => horizontalH1Gradient Q hQ f j + horizontalH1Gradient Q hQ g j) hadd) i
/-- Source main.tex240–248: the chosen horizontal gradient is homogeneous on the domain. -/
theorem horizontalH1Gradient_smul {d : ℕ} (Q : Measure (FieldPair d)) (hQ : IsStationary Q)
    (c : ℝ) (f : horizontalH1 Q hQ) (i : Fin d) :
    horizontalH1Gradient Q hQ (c • f) i = c • horizontalH1Gradient Q hQ f i := by
  have hsmul : ∀ j : Fin d,
      HasHorizontalLpDerivative Q hQ j ((c • f : horizontalH1 Q hQ) : Lp ℝ 2 Q)
        (c • horizontalH1Gradient Q hQ f j) := fun j => by
    rw [Submodule.coe_smul]
    exact (hasHorizontalLpDerivative_horizontalH1Gradient Q hQ f j).smul c
  exact congrFun (horizontalH1Gradient_eq_of_hasHorizontalLpDerivative Q hQ (c • f)
    (fun j => c • horizontalH1Gradient Q hQ f j) hsmul) i
end EinsteinRelation
