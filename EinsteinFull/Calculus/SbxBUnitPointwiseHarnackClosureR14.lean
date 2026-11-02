import EinsteinFull.Calculus.SbxBUnitHarnackClosureR13
import EinsteinFull.Calculus.SbxBWeightedNestedHarnackR11

namespace EinsteinFull.Calculus

/-- Uniform unit-cylinder pointwise Harnack inequality for weighted caloric fields. -/
theorem b_unit_pointwise_harnack_r14 (d : ℕ) (hd : 2 ≤ d)
    (κ : ℝ) (hκ : 0 < κ) : BUnitPointwiseHarnack d κ :=
  b_unit_pointwise_harnack_of_native_weak_r13 d hd κ hκ
    (b_native_unit_weak_harnack d hd κ hκ)

#print axioms b_unit_pointwise_harnack_r14

end EinsteinFull.Calculus
