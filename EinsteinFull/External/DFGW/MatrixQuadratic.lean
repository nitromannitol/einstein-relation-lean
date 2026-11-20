import EinsteinFull.External.DFGW.MartingaleCovariance

/-! # Quadratic forms of matrix differences

The quadratic form of a matrix difference expands into the corresponding weighted sum
of its entries.
-/

open EinsteinRelation
open scoped BigOperators

namespace EinsteinFull.External.DFGW

/-- The quadratic form of a matrix with entries `Cᵢⱼ - 2 Kᵢⱼ`. -/
theorem dot_matrix_sub_two_mul {d : ℕ} (C K : Mat d) (e : Vec d) :
    dot e (Matrix.mulVec ((fun i j => C i j - 2 * K i j) : Mat d) e) =
      dot e (C.mulVec e) - 2 * ∑ i : Fin d, ∑ j : Fin d, (e i * e j) * K i j := by
  change (∑ i : Fin d, e i * ∑ j : Fin d, (C i j - 2 * K i j) * e j) =
    (∑ i : Fin d, e i * ∑ j : Fin d, C i j * e j) -
      2 * ∑ i : Fin d, ∑ j : Fin d, (e i * e j) * K i j
  simp only [sub_mul, Finset.sum_sub_distrib, mul_sub, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

end EinsteinFull.External.DFGW
