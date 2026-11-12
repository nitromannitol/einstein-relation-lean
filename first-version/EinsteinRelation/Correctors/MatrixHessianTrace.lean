import EinsteinRelation.Correctors.LinearKernelCalculus

/-! # Whitening a Hessian contraction by trace cyclicity

Source: `paper/main.tex:1003–1018`. The coefficient matrix and inverse
square-root coordinates reduce the transformed spatial operator to a trace.
-/

open scoped BigOperators
noncomputable section
namespace EinsteinRelation.Correctors.KernelCalculus

/-- The whitened Hessian contraction is its ordinary trace
(`paper/main.tex:1003–1018`). -/
theorem matrix_hessian_contraction_trace {d : ℕ} (A B H : Mat d)
    (hBA : B * A * B.transpose = 1) :
    (∑ i, ∑ j, A i j * (∑ a, ∑ b, B a j * B b i * H b a)) =
      ∑ a, H a a := by
  calc
    _ = Matrix.trace (A * (B.transpose * (H.transpose * B))) := by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = Matrix.trace ((B * A * B.transpose) * H.transpose) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace H.transpose := by rw [hBA, Matrix.one_mul]
    _ = _ := by simp only [Matrix.trace, Matrix.diag, Matrix.transpose_apply]

end EinsteinRelation.Correctors.KernelCalculus
