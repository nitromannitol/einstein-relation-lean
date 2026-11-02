import EinsteinFull.Frozen.ComplexTranslation

open MeasureTheory Filter
open scoped Topology

namespace EinsteinFull

open EinsteinRelation

/-- The domain/value relation for the horizontal generator in direction `e_i`:
the two-sided strong derivative of the actual complex `L²` translation group. -/
def HasComplexHorizontalDerivative {d : ℕ} (Q : Measure (FieldPair d))
    (hQ : IsStationary Q) (i : Fin d) (f g : Lp ℂ 2 Q) : Prop :=
  Tendsto (fun t : ℝ => (t : ℂ)⁻¹ •
    (complexTranslation Q hQ (t • unitVector i) f - f))
    (𝓝[≠] (0 : ℝ)) (𝓝 g)

end EinsteinFull
