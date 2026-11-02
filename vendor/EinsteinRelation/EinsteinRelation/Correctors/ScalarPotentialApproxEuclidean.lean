import EinsteinRelation.Correctors.StationarySpatialRealizationSupport
open MeasureTheory
namespace EinsteinRelation.Correctors.ScalarPotentialApproximation
/-- Euclidean energy agrees with the actual L²-vector energy; paper/main.tex:693-698. -/
theorem euclideanSq_ofLp_sub_eq_norm_sq {d : ℕ}
    (v w : EuclideanSpace ℝ (Fin d)) :
    euclideanSq (v.ofLp - w.ofLp) = ‖v - w‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  unfold euclideanSq dot
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.sub_apply, PiLp.sub_apply, Real.norm_eq_abs, sq_abs, sq, abs_mul_abs_self]
end EinsteinRelation.Correctors.ScalarPotentialApproximation
