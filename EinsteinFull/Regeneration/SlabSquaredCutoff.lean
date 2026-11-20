import EinsteinFull.Regeneration.SlabCutoffPointwise
import EinsteinFull.Regeneration.SlabCollarPointwise

/-!
# The squared transverse slab cutoff

The concrete cutoff competitor satisfies the pointwise absorption estimate
with its explicit transverse gradient constant.
-/

open Set PDE

namespace EinsteinFull.Regeneration

/-- The squared transverse-cutoff competitor has an absorbable energy error. -/
theorem slab_squared_cutoff_pointwise_energy_le
    {n : ℕ} {U : Set (PDE.Vec (n + 1))}
    (hU : PDE.IsOpenBoundedConvexDomain U) (u : PDE.H1Function U)
    (i : Fin (n + 1)) (L s : ℝ) (a b : PDE.Vec (n + 1))
    (w : ℝ) (hw : 0 < w) (x : PDE.Vec (n + 1)) (hx : x ∈ PDE.axisBox a b)
    (A : PDE.Mat (n + 1)) (lam Λ : ℝ) (hA : PDE.IsEllipticMatrix lam Λ A)
    (hsym : A.IsSymm) :
    let η := slabTransverseCutoff i a b w hw
    let p := slabBoundaryProfile hU i L
    matrixEnergy (Real.exp (s * x i) • A)
      (u.grad x + (slabCutoffPerturbation hU u i L η.sq).grad x) ≤
      Real.exp (s * x i) *
        ((1 - η x ^ 2 / 2) * matrixEnergy A (u.grad x) +
          (3 * η x ^ 2 / 2) * matrixEnergy A (p.grad x) +
          (Λ + 4 * Λ ^ 2 / lam) * (4 * ((32 * (n + 1 : ℝ)) / w) ^ 2) *
            (p x - u x) ^ 2) := by
  dsimp only
  let η := slabTransverseCutoff i a b w hw
  let p := slabBoundaryProfile hU i L
  let K : ℝ := (32 * (n + 1 : ℝ)) / w
  let z : PDE.Vec (n + 1) := (2 * (p x - u x)) • PDE.classicalGradient η.toFun x
  have hgrad : u.grad x + (slabCutoffPerturbation hU u i L η.sq).grad x =
      η x ^ 2 • p.grad x + (1 - η x ^ 2) • u.grad x + η x • z := by
    rw [slabCutoff_competitor_grad, PDE.QuantitativeSmoothCutoff.sq_apply,
      PDE.QuantitativeSmoothCutoff.sq_classicalGradient]
    dsimp only [z]
    ext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hηgrad : PDE.vecEuclideanNorm (PDE.classicalGradient η.toFun x) ≤ K := by
    simpa only [η, K, Nat.cast_add, Nat.cast_one] using
      slabTransverseCutoff_gradient_le i a b w hw hx
  have hz : PDE.vecEuclideanNorm z ≤ 2 * |p x - u x| * K := by
    dsimp only [z]
    rw [PDE.vecEuclideanNorm_smul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_left hηgrad (by positivity)
  have hzsq : (PDE.vecEuclideanNorm z) ^ 2 ≤ 4 * K ^ 2 * (p x - u x) ^ 2 := by
    have h := pow_le_pow_left₀ (PDE.vecEuclideanNorm_nonneg z) hz 2
    nlinarith [sq_abs (p x - u x)]
  have hcoef : 0 ≤ Λ + 4 * Λ ^ 2 / lam :=
    add_nonneg hA.Lam_pos.le (div_nonneg (by positivity) hA.lam_pos.le)
  have h := matrixEnergy_squared_cutoff_le hA hsym (η x) (η.nonneg x) (η.le_one x)
    (p.grad x) (u.grad x) z
  have herr := mul_le_mul_of_nonneg_left hzsq hcoef
  have hpoint : matrixEnergy A (η x ^ 2 • p.grad x + (1 - η x ^ 2) • u.grad x + η x • z) ≤
      (1 - η x ^ 2 / 2) * matrixEnergy A (u.grad x) +
        (3 * η x ^ 2 / 2) * matrixEnergy A (p.grad x) +
        (Λ + 4 * Λ ^ 2 / lam) * (4 * K ^ 2) * (p x - u x) ^ 2 := by
    nlinarith only [h, herr]
  rw [hgrad, matrixEnergy_smul_matrix]
  exact mul_le_mul_of_nonneg_left hpoint (Real.exp_pos _).le

end EinsteinFull.Regeneration
