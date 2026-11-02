import EinsteinRelation.Environment.MatrixNorm

/-! Source: `paper/main.tex:716-723`. Frobenius norm under the physical amplitude. -/
namespace EinsteinRelation.Correctors

/-- Physical amplitude scaling retains the Euclidean tensor norm. -/
theorem frobeniusNorm_smul {d : ℕ} (c : ℝ) (A : Mat d) :
    frobeniusNorm (c • A) = |c| * frobeniusNorm A := by
  have heq : frobeniusSq (c • A) = c ^ 2 * frobeniusSq A := by
    simp only [frobeniusSq, Matrix.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [frobeniusNorm, heq, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]
  rfl

/-- Squared Frobenius norms are the finite sum of the entrywise squares. -/
theorem frobeniusNorm_sq_eq_sum {d : ℕ} (A : Mat d) :
    frobeniusNorm A ^ 2 = ∑ j : Fin d, ∑ k : Fin d, (A j k) ^ 2 := by
  rw [frobeniusNorm, Real.sq_sqrt (frobeniusSq_nonneg _)]
  simp only [frobeniusSq, pow_two]

end EinsteinRelation.Correctors
