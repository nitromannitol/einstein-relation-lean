import EinsteinRelation.Calculus.Weak
import EinsteinRelation.Regeneration.HalfSpaces

/-!
# Restriction of scalar-potential approximations

Source: `paper/main.tex:699-704,735-737`. Compact spatial convergence
restricts to the Euclidean balls used by the scalar-potential limit.
-/

open MeasureTheory
namespace EinsteinRelation.Correctors.ScalarPotentialApproximation

/-- A Euclidean ball lies inside the compact coordinate closed ball of the same radius. -/
theorem euclideanBall_subset_coordinateClosedBall {d : ℕ} (R : ℝ) (hR : 0 ≤ R) :
    {x : Vec d | euclideanNorm (x - 0) < R} ⊆ Metric.closedBall (0 : Vec d) R := by
  intro x hx
  have hx' : euclideanNorm x < R := by simpa only [sub_zero] using hx
  rw [Metric.mem_closedBall, dist_pi_le_iff hR]
  intro i
  simpa only [Real.dist_eq, Pi.zero_apply, sub_zero] using
    (Regeneration.coordinate_abs_le_euclideanNorm x i).trans hx'.le

private theorem test_eq_zero_outside {d : ℕ} {U : Set (Vec d)} {φ : Vec d → ℝ}
    (hφ : IsSpatialTest U φ) {x : Vec d} (hx : x ∉ U) : φ x = 0 :=
  (notMem_tsupport_iff_eventuallyEq.mp (fun ht => hx (hφ.2.2 ht))).self_of_nhds

private theorem test_derivative_eq_zero_outside {d : ℕ} {U : Set (Vec d)}
    {φ : Vec d → ℝ} (hφ : IsSpatialTest U φ) (i : Fin d) {x : Vec d}
    (hx : x ∉ U) : coordinateDerivative i φ x = 0 := by
  simp only [coordinateDerivative, fderiv_of_notMem_tsupport ℝ (fun ht => hx (hφ.2.2 ht)),
    ContinuousLinearMap.zero_apply]

/-- The genuine spatial weak-gradient identity restricts to every spatial domain. -/
theorem hasWeakGradient_restrict_univ {d : ℕ} (U : Set (Vec d))
    {u : Vec d → ℝ} {g : Vec d → Vec d}
    (h : HasWeakGradient Set.univ u g) : HasWeakGradient U u g := by
  intro i
  refine ⟨(h i).1.mono_set (Set.subset_univ _),
    (h i).2.1.mono_set (Set.subset_univ _), ?_⟩
  intro φ hφ
  have hl := setIntegral_eq_of_subset_of_forall_diff_eq_zero (μ := volume)
    MeasurableSet.univ (Set.subset_univ U)
    (f := fun x => u x * coordinateDerivative i φ x)
    (fun x hx => by
      change u x * coordinateDerivative i φ x = 0
      rw [test_derivative_eq_zero_outside hφ i hx.2, mul_zero])
  have hr := setIntegral_eq_of_subset_of_forall_diff_eq_zero (μ := volume)
    MeasurableSet.univ (Set.subset_univ U)
    (f := fun x => g x i * φ x)
    (fun x hx => by
      change g x i * φ x = 0
      rw [test_eq_zero_outside hφ hx.2, mul_zero])
  rw [← hl, ← hr]
  exact (h i).2.2 φ ⟨hφ.1, hφ.2.1, Set.subset_univ _⟩

end EinsteinRelation.Correctors.ScalarPotentialApproximation
