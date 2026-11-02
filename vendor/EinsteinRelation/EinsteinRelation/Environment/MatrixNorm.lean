import EinsteinRelation.Environment.Basic

/-! # Euclidean norm of the flux-corrector tensor

Matrix-valued corrector estimates use the Frobenius norm. The operator norm
in the coefficient Lipschitz assumption remains a separate condition.
-/

open scoped BigOperators

namespace EinsteinRelation

/-- Sum of squares of every matrix entry. -/
def frobeniusSq {d : ℕ} (A : Mat d) : ℝ := ∑ i, ∑ j, A i j * A i j

/-- Euclidean (Frobenius) norm of a matrix, with no new matrix norm instance. -/
noncomputable def frobeniusNorm {d : ℕ} (A : Mat d) : ℝ := Real.sqrt (frobeniusSq A)

theorem frobeniusSq_nonneg {d : ℕ} (A : Mat d) : 0 ≤ frobeniusSq A :=
  Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => mul_self_nonneg (A i j)))

theorem frobeniusSq_transpose {d : ℕ} (A : Mat d) :
    frobeniusSq A.transpose = frobeniusSq A := by
  unfold frobeniusSq
  exact Finset.sum_comm

theorem frobeniusNorm_transpose {d : ℕ} (A : Mat d) :
    frobeniusNorm A.transpose = frobeniusNorm A := by
  rw [frobeniusNorm, frobeniusNorm, frobeniusSq_transpose]

end EinsteinRelation
