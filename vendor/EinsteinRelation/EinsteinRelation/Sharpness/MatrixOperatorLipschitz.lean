import EinsteinRelation.Environment.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
namespace EinsteinRelation.Sharpness
private theorem opLip_coord {d : ℕ} (k : Fin d) (v : Vec d) : |v k| ≤ euclideanNorm v := by
  unfold euclideanNorm
  apply Real.abs_le_sqrt
  unfold euclideanSq dot
  rw [pow_two]
  exact Finset.single_le_sum (f := fun j => v j * v j) (fun j _ => mul_self_nonneg _) (Finset.mem_univ k)
private theorem opLip_norm_le_sum {d : ℕ} (v : Vec d) : euclideanNorm v ≤ ∑ j, |v j| := by
  have hS : 0 ≤ ∑ j, |v j| := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hs : euclideanSq v ≤ (∑ j, |v j|)^2 := by
    unfold euclideanSq dot
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j _
    have hj : |v j| ≤ ∑ k, |v k| := Finset.single_le_sum (fun k _ => abs_nonneg (v k)) (Finset.mem_univ j)
    calc v j * v j = |v j| * |v j| := (abs_mul_abs_self _).symm
      _ ≤ |v j| * ∑ k, |v k| := mul_le_mul_of_nonneg_left hj (abs_nonneg _)
  exact (Real.sqrt_le_sqrt hs).trans_eq (Real.sqrt_sq hS)
/-- Source main.tex1218–1231: entrywise spatial bounds imply a literal Euclidean operator bound.
The finite-coordinate dimension factor introduces no matrix norm instance. -/
theorem isOperatorLipschitz_of_entrywise {d : ℕ} (a : Vec d → Mat d) (L : ℝ) (hL : 0 ≤ L)
    (hentry : ∀ x y j k, |a x j k - a y j k| ≤ L * euclideanNorm (x-y)) :
    IsOperatorLipschitz ((d : ℝ)^2 * L) a := by
  intro x y ξ
  have hD : 0 ≤ euclideanNorm (x-y) := Real.sqrt_nonneg _
  calc
    euclideanNorm ((a x-a y).mulVec ξ) ≤ ∑ j, |((a x-a y).mulVec ξ) j| := opLip_norm_le_sum _
    _ ≤ ∑ _j : Fin d, ∑ _k : Fin d, L * euclideanNorm (x-y) * euclideanNorm ξ := by
      apply Finset.sum_le_sum
      intro j _
      change |∑ k : Fin d, (a x j k - a y j k) * ξ k| ≤ _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      exact mul_le_mul (hentry x y j k) (opLip_coord k ξ) (abs_nonneg _) (mul_nonneg hL hD)
    _ = _ := by simp; ring
end EinsteinRelation.Sharpness
