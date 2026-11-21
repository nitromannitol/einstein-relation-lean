import EinsteinFull.Regeneration.SlabCutoffPerturbation
import EinsteinFull.Regeneration.SlabTransverseCutoff
import EinsteinFull.Regeneration.ConvexEllipticEnergy

/-!
# Pointwise energy of the slab cutoff competitor

The product rule and convex elliptic energy give the explicit squared and
mixed errors appearing on a transverse shell.
-/

open Set PDE

namespace EinsteinFull.Regeneration

/-- Scaling a coefficient matrix scales its quadratic energy. -/
theorem matrixEnergy_smul_matrix {d : ℕ} (A : PDE.Mat d) (c : ℝ) (v : PDE.Vec d) :
    matrixEnergy (c • A) v = c * matrixEnergy A v := by
  unfold matrixEnergy
  rw [show PDE.matVecMul (c • A) v = c • PDE.matVecMul A v from Matrix.smul_mulVec c A v,
    PDE.DGNM.vecDot_smul_left]

/-- The actual competitor gradient is a convex mixture plus the cutoff error. -/
theorem slabCutoff_competitor_grad {n : ℕ} {U inner outer : Set (PDE.Vec (n + 1))}
    {C : ℝ} (hU : PDE.IsOpenBoundedConvexDomain U) (u : PDE.H1Function U)
    (i : Fin (n + 1)) (L : ℝ) (η : PDE.QuantitativeSmoothCutoff inner outer C)
    (x : PDE.Vec (n + 1)) :
    u.grad x + (slabCutoffPerturbation hU u i L η).grad x =
      η x • (slabBoundaryProfile hU i L).grad x + (1 - η x) • u.grad x +
        (slabBoundaryProfile hU i L x - u x) • PDE.classicalGradient η.toFun x := by
  simp only [slabCutoffPerturbation, PDE.H1Function.mulCutoff_grad, PDE.H1Function.sub_grad,
    PDE.H1Function.sub_toFun]
  ext j
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The cutoff competitor satisfies the weighted pointwise shell-energy bound. -/
theorem slab_cutoff_pointwise_energy_le {n : ℕ} {U : Set (PDE.Vec (n + 1))}
    (hU : PDE.IsOpenBoundedConvexDomain U) (u : PDE.H1Function U)
    (i : Fin (n + 1)) (L s : ℝ) (a b : PDE.Vec (n + 1))
    (w : ℝ) (hw : 0 < w) (x : PDE.Vec (n + 1)) (hx : x ∈ PDE.axisBox a b)
    (A : PDE.Mat (n + 1)) (lam Λ : ℝ) (hA : PDE.IsEllipticMatrix lam Λ A)
    (hsym : A.IsSymm) :
    matrixEnergy (Real.exp (s * x i) • A)
      (u.grad x + (slabCutoffPerturbation hU u i L (slabTransverseCutoff i a b w hw)).grad x) ≤
      Real.exp (s * x i) *
        (matrixEnergy A ((slabBoundaryProfile hU i L).grad x) + matrixEnergy A (u.grad x) +
          Λ * ((32 * (n + 1 : ℝ)) / w) ^ 2 * (slabBoundaryProfile hU i L x - u x) ^ 2 +
          2 * Λ * ((32 * (n + 1 : ℝ)) / w) * |slabBoundaryProfile hU i L x - u x| *
            (PDE.vecEuclideanNorm ((slabBoundaryProfile hU i L).grad x) +
              PDE.vecEuclideanNorm (u.grad x))) := by
  let η := slabTransverseCutoff i a b w hw
  let p := slabBoundaryProfile hU i L
  let K : ℝ := (32 * (n + 1 : ℝ)) / w
  let z : PDE.Vec (n + 1) := (p x - u x) • PDE.classicalGradient η.toFun x
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hgrad : PDE.vecEuclideanNorm (PDE.classicalGradient η.toFun x) ≤ K :=
    by simpa only [η, K, Nat.cast_add, Nat.cast_one] using
      slabTransverseCutoff_gradient_le i a b w hw hx
  have hz : PDE.vecEuclideanNorm z ≤ K * |p x - u x| := by
    dsimp only [z]
    rw [PDE.vecEuclideanNorm_smul]
    have h := mul_le_mul_of_nonneg_left hgrad (abs_nonneg (p x - u x))
    nlinarith
  have hz0 := PDE.vecEuclideanNorm_nonneg z
  have hN : 0 ≤ PDE.vecEuclideanNorm (p.grad x) + PDE.vecEuclideanNorm (u.grad x) :=
    add_nonneg (PDE.vecEuclideanNorm_nonneg _) (PDE.vecEuclideanNorm_nonneg _)
  have hzsq : (PDE.vecEuclideanNorm z) ^ 2 ≤ K ^ 2 * (p x - u x) ^ 2 := by
    have h := pow_le_pow_left₀ hz0 hz 2
    simpa only [mul_pow, sq_abs] using h
  have hcross : 2 * Λ * PDE.vecEuclideanNorm z *
      (PDE.vecEuclideanNorm (p.grad x) + PDE.vecEuclideanNorm (u.grad x)) ≤
      2 * Λ * K * |p x - u x| *
        (PDE.vecEuclideanNorm (p.grad x) + PDE.vecEuclideanNorm (u.grad x)) := by
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hz (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hA.Lam_pos.le)) hN
    nlinarith
  have h := matrixEnergy_convex_add_le hA hsym (η x) (η.nonneg x) (η.le_one x)
    (p.grad x) (u.grad x) z
  have hscalar : matrixEnergy A (η x • p.grad x + (1 - η x) • u.grad x + z) ≤
      matrixEnergy A (p.grad x) + matrixEnergy A (u.grad x) +
        Λ * K ^ 2 * (p x - u x) ^ 2 +
        2 * Λ * K * |p x - u x| *
          (PDE.vecEuclideanNorm (p.grad x) + PDE.vecEuclideanNorm (u.grad x)) := by
    nlinarith [h, hcross, mul_le_mul_of_nonneg_left hzsq hA.Lam_pos.le]
  rw [slabCutoff_competitor_grad, matrixEnergy_smul_matrix]
  exact mul_le_mul_of_nonneg_left hscalar (Real.exp_pos _).le


/-- At any point where a cutoff reaches one, its gradient vanishes. -/
theorem cutoff_gradient_eq_zero_of_eq_one {d : ℕ} {inner outer : Set (PDE.Vec d)}
    {C : ℝ} (η : PDE.QuantitativeSmoothCutoff inner outer C)
    (x : PDE.Vec d) (hx : η x = 1) : PDE.classicalGradient η.toFun x = 0 := by
  have hmax : IsMaxOn η.toFun Set.univ x := by
    intro y _
    rw [hx]
    exact η.le_one y
  have hfderiv : fderiv ℝ η.toFun x = 0 :=
    (hmax.isLocalMax (by simp)).fderiv_eq_zero
  funext j
  rw [PDE.classicalGradient_apply, hfderiv]
  exact zero_apply _

/-- Where the cutoff is one, the actual competitor has the profile gradient. -/
theorem slabCutoff_competitor_grad_of_eq_one
    {n : ℕ} {U inner outer : Set (PDE.Vec (n + 1))} {C : ℝ}
    (hU : PDE.IsOpenBoundedConvexDomain U) (u : PDE.H1Function U)
    (i : Fin (n + 1)) (L : ℝ) (η : PDE.QuantitativeSmoothCutoff inner outer C)
    (x : PDE.Vec (n + 1)) (hx : η x = 1) :
    u.grad x + (slabCutoffPerturbation hU u i L η).grad x =
      (slabBoundaryProfile hU i L).grad x := by
  rw [slabCutoff_competitor_grad, hx, cutoff_gradient_eq_zero_of_eq_one η x hx]
  simp

/-- The mixed cutoff error can be absorbed into squared-value and gradient errors. -/
theorem slab_cutoff_pointwise_energy_le_squared {n : ℕ} {U : Set (PDE.Vec (n + 1))}
    (hU : PDE.IsOpenBoundedConvexDomain U) (u : PDE.H1Function U)
    (i : Fin (n + 1)) (L s : ℝ) (a b : PDE.Vec (n + 1))
    (w : ℝ) (hw : 0 < w) (x : PDE.Vec (n + 1)) (hx : x ∈ PDE.axisBox a b)
    (A : PDE.Mat (n + 1)) (lam Λ : ℝ) (hA : PDE.IsEllipticMatrix lam Λ A)
    (hsym : A.IsSymm) :
    matrixEnergy (Real.exp (s * x i) • A)
      (u.grad x + (slabCutoffPerturbation hU u i L (slabTransverseCutoff i a b w hw)).grad x) ≤
      Real.exp (s * x i) *
        (matrixEnergy A ((slabBoundaryProfile hU i L).grad x) + matrixEnergy A (u.grad x) +
          Λ * (((32 * (n + 1 : ℝ)) / w) ^ 2 + ((32 * (n + 1 : ℝ)) / w)) *
            (slabBoundaryProfile hU i L x - u x) ^ 2 +
          2 * Λ * ((32 * (n + 1 : ℝ)) / w) *
            (PDE.vecNormSq ((slabBoundaryProfile hU i L).grad x) + PDE.vecNormSq (u.grad x))) := by
  let K : ℝ := (32 * (n + 1 : ℝ)) / w
  let v := (slabBoundaryProfile hU i L).grad x
  let g := u.grad x
  let D := slabBoundaryProfile hU i L x - u x
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hmix : 2 * |D| * (PDE.vecEuclideanNorm v + PDE.vecEuclideanNorm g) ≤
      D ^ 2 + 2 * (PDE.vecNormSq v + PDE.vecNormSq g) := by
    have h1 := sq_nonneg (|D| - (PDE.vecEuclideanNorm v + PDE.vecEuclideanNorm g))
    have h2 := sq_nonneg (PDE.vecEuclideanNorm v - PDE.vecEuclideanNorm g)
    have hv := PDE.vecEuclideanNorm_sq v
    have hg := PDE.vecEuclideanNorm_sq g
    nlinarith [sq_abs D]
  have hscaled := mul_le_mul_of_nonneg_left hmix (mul_nonneg hA.Lam_pos.le hK)
  have hbase := slab_cutoff_pointwise_energy_le hU u i L s a b w hw x hx A lam Λ hA hsym
  have hpoint : matrixEnergy A v + matrixEnergy A g + Λ * K ^ 2 * D ^ 2 +
      2 * Λ * K * |D| * (PDE.vecEuclideanNorm v + PDE.vecEuclideanNorm g) ≤
      matrixEnergy A v + matrixEnergy A g + Λ * (K ^ 2 + K) * D ^ 2 +
        2 * Λ * K * (PDE.vecNormSq v + PDE.vecNormSq g) := by nlinarith [hscaled]
  exact hbase.trans (mul_le_mul_of_nonneg_left hpoint (Real.exp_pos _).le)

end EinsteinFull.Regeneration
