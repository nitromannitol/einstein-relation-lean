import EinsteinFull.Frozen.ComplexHorizontalDerivative

open MeasureTheory

namespace EinsteinFull

open EinsteinRelation

/-- The actual horizontal `H¹` gradient relation of Section 2. No representative
or gradient is selected, and no estimate is included in this predicate. -/
def HasComplexHorizontalGradient {d : ℕ} (Q : Measure (FieldPair d))
    (hQ : IsStationary Q) (f : Lp ℂ 2 Q) (G : Fin d → Lp ℂ 2 Q) : Prop :=
  ∀ i : Fin d, HasComplexHorizontalDerivative Q hQ i f (G i)

end EinsteinFull
