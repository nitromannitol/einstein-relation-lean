import EinsteinFull.Regeneration.SlabBoxWeightTransfer
import EinsteinFull.Regeneration.SlabWeightedIntegrability

/-!
# Initial slab profile error

The solution and the comparison profile both lie in the unit interval, so
their weighted squared difference is controlled by the full slab weight.
-/

open MeasureTheory Set PDE

namespace EinsteinFull.Regeneration

/-- The full weighted profile error on a source subbox has the initial rate. -/
theorem slab_profile_value_error_le_initial_rate
    {n : ℕ} {U : Set (PDE.Vec (n + 1))}
    (hU : PDE.IsOpenBoundedConvexDomain U) (u : PDE.H1Function U)
    (i : Fin (n + 1)) (L s : ℝ) (hs : 0 < s) (a b : PDE.Vec (n + 1))
    (hQ : PDE.axisBox a b ⊆ coordinateSlabBox n i s L)
    (hcont : Continuous u.toFun) (hzero : ∀ x, 0 ≤ u x) (hone : ∀ x, u x ≤ 1) :
    (∫ x in PDE.axisBox a b, Real.exp (s * x i) *
      (slabBoundaryProfile hU i L x - u x) ^ 2) ≤
      ((2 : ℝ) ^ n / s) * Real.exp ((s * (2 * (n + 1 : ℝ) - 1) / (n + 1)) * L) := by
  apply coordinate_subslab_integral_le_weight n i s L hs (PDE.axisBox a b)
    (PDE.isOpen_axisBox _ _).measurableSet hQ _
    (integrableOn_box_weighted_profile_error hU u hcont a b i L s)
  intro x _
  have hp := slabBoundaryProfile_mem_Icc hU i L x
  have hdiff : (slabBoundaryProfile hU i L x - u x) ^ 2 ≤ 1 := by
    nlinarith [hzero x, hone x, hp.1, hp.2,
      mul_nonneg (show 0 ≤ 1 - (slabBoundaryProfile hU i L x - u x) by
        linarith [hp.2, hzero x])
        (show 0 ≤ 1 + (slabBoundaryProfile hU i L x - u x) by
          linarith [hp.1, hone x])]
  have h := mul_le_mul_of_nonneg_left hdiff (Real.exp_pos (s * x i)).le
  simpa only [mul_one] using h

end EinsteinFull.Regeneration
