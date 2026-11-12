import EinsteinRelation.Calculus.CoordinatePathAverage

/-! # Euclidean moments of the small-scale residual flux

Source: `paper/main.tex:1028–1029`. The coordinate path construction has
a uniform Euclidean moment controlled by the compact averaging radius.
-/

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace EinsteinRelation

/-- The literal small-scale flux obeys the manuscript's Euclidean bound
(`paper/main.tex:1028–1029`). -/
theorem eLpNorm_coordinatePathAverage_euclidean_le {d : ℕ}
    {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {p L C : ℝ} (hp : 2 ≤ p) (hL : 0 ≤ L) (hC : 0 ≤ C)
    {K : Vec d → ℝ} (hK : Measurable K) (hKi : Integrable K volume)
    (hKn : ∀ z, 0 ≤ K z) (hKm : (∫ z, K z) = 1)
    (hKt : ∀ z, L ≤ euclideanNorm z → K z = 0)
    {f : FieldPair d → ℝ} (hf : Measurable f)
    (hfb : eLpNorm f (ENNReal.ofReal p) Q ≤ ENNReal.ofReal C) :
    eLpNorm (fun ω => euclideanNorm (coordinatePathAverage K f ω))
      (ENNReal.ofReal p) Q ≤ ENNReal.ofReal (Real.sqrt d * (L * C)) := by
  apply Correctors.eLpNorm_euclideanNorm_le_of_coordinate_bounds Q hp (mul_nonneg hL hC)
    (measurable_coordinatePathAverage hK hf)
  intro i
  exact eLpNorm_coordinatePathAverage_coordinate_le hQ
    (ENNReal.one_le_ofReal.mpr (by linarith)) ENNReal.ofReal_ne_top hL
    hK hKi hKn hKm hKt hf hfb i

end EinsteinRelation
