import EinsteinFull.External.DFGW.MartingaleCovariance

/-! # Symmetric matrices determined by their quadratic forms

A symmetric real matrix is uniquely determined by its quadratic form.
-/

open EinsteinRelation
open scoped BigOperators

namespace EinsteinFull.External.DFGW

/-- Symmetric matrices with the same quadratic form are equal. -/
theorem symmetric_matrix_eq_of_quadratic {d : ℕ} (A B : Mat d)
    (hA : A.transpose = A) (hB : B.transpose = B)
    (h : ∀ e : Vec d, dot e (A.mulVec e) = dot e (B.mulVec e)) : A = B := by
  classical
  ext i j
  have hii := h (unitVector i)
  have hjj := h (unitVector j)
  have hij := h (unitVector i + unitVector j)
  have hsA : A j i = A i j := congrFun (congrFun hA i) j
  have hsB : B j i = B i j := congrFun (congrFun hB i) j
  simp only [dot, unitVector, Matrix.mulVec, dotProduct, Pi.add_apply, Pi.single_apply,
    add_mul, mul_add, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hii hjj hij
  linarith

end EinsteinFull.External.DFGW
