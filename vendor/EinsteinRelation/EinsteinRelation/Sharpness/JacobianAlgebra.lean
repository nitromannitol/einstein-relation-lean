import EinsteinRelation.Environment.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.RowCol
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-! # Algebra of the sharpness Jacobian

Finite-dimensional algebra from `paper/main.tex`, proof of `sharp.example`, Steps 1, 2 and 4
(lines 1219–1264). For a coordinate `i₁` put `e = unitVector i₁`. For a vector `g` with
`euclideanNorm g ≤ 1/4`, the matrix `J g = 1 + e ⊗ g` is the Jacobian of `x ↦ x + g(x) e`
(`eq.sharp-map`), its determinant is `jac g = 1 + g i₁`, and `sharpCoeff g` is the coefficient
`j J⁻¹ J⁻ᵀ` of `eq.sharp-coefficients`.

The results are: the determinant and the inverse (Step 1); the symmetry and the identity
`a (e + g) = e` (`eq.sharp-harmonic`, Step 2); the entry `a_{i₁ i₁}` and the pairing
`a e · g` used for `eq.sharp-constant` (Step 4); and uniform ellipticity with the explicit
constants `1/4` and `20/9`.
-/

open scoped Matrix

namespace EinsteinRelation.Sharpness

variable {d : ℕ}

/-- The Jacobian `J g = 1 + e ⊗ g` with `e = unitVector i₁`, so `(J g) i j = δ i j + e i * g j`. -/
def sharpJ (i₁ : Fin d) (g : Vec d) : Mat d :=
  1 + Matrix.vecMulVec (unitVector i₁) g

/-- The Jacobian determinant `jac g = 1 + g i₁`. -/
def sharpJac (i₁ : Fin d) (g : Vec d) : ℝ :=
  1 + g i₁

/-- The coefficient `jac g • (J g)⁻¹ ((J g)⁻¹)ᵀ`, that is `j J⁻¹ J⁻ᵀ` with `j = det J`. -/
noncomputable def sharpCoeff (i₁ : Fin d) (g : Vec d) : Mat d :=
  sharpJac i₁ g • ((sharpJ i₁ g)⁻¹ * ((sharpJ i₁ g)⁻¹)ᵀ)

/-! ### Scalar and coordinate estimates -/

private theorem sharp_dot_eq (x y : Vec d) : dot x y = dotProduct x y := rfl

private theorem sharp_euclideanSq_eq (x : Vec d) : euclideanSq x = dotProduct x x := rfl

private theorem sharp_dotProduct_unitVector (x : Vec d) (i : Fin d) :
    dotProduct x (unitVector i) = x i := by
  simp [unitVector, dotProduct_single]

private theorem sharp_unitVector_dotProduct (i : Fin d) (x : Vec d) :
    dotProduct (unitVector i) x = x i := by
  simp [unitVector, single_dotProduct]

private theorem sharp_dot_self_nonneg (x : Vec d) : 0 ≤ dot x x := by
  unfold dot
  exact Finset.sum_nonneg fun k _ => mul_self_nonneg (x k)

private theorem sharp_euclideanSq_nonneg (x : Vec d) : 0 ≤ euclideanSq x :=
  sharp_dot_self_nonneg x

private theorem sharp_sq_coord_le (i : Fin d) (x : Vec d) : x i * x i ≤ euclideanSq x := by
  unfold euclideanSq dot
  exact Finset.single_le_sum (f := fun k => x k * x k) (fun k _ => mul_self_nonneg (x k))
    (Finset.mem_univ i)

private theorem sharp_euclideanSq_le_sixteenth {x : Vec d} (hx : euclideanNorm x ≤ 1 / 4) :
    euclideanSq x ≤ 1 / 16 := by
  have hsq : euclideanNorm x ^ 2 = euclideanSq x := by
    unfold euclideanNorm
    exact Real.sq_sqrt (sharp_euclideanSq_nonneg x)
  have hn : 0 ≤ euclideanNorm x := by
    unfold euclideanNorm
    exact Real.sqrt_nonneg _
  nlinarith [mul_nonneg hn (sub_nonneg.mpr hx)]

private theorem sharp_coord_bounds (i : Fin d) {g : Vec d} (hg : euclideanNorm g ≤ 1 / 4) :
    -(1 / 4) ≤ g i ∧ g i ≤ 1 / 4 := by
  have h : g i * g i ≤ 1 / 16 :=
    le_trans (sharp_sq_coord_le i g) (sharp_euclideanSq_le_sixteenth hg)
  constructor
  · nlinarith [sq_nonneg (g i + 1 / 4)]
  · nlinarith [sq_nonneg (g i - 1 / 4)]

/-- Step 1 of `sharp.example`: the Jacobian factor lies in `[3/4, 5/4]`. -/
theorem sharpJac_bounds (i₁ : Fin d) (g : Vec d) (hg : euclideanNorm g ≤ 1 / 4) :
    3 / 4 ≤ sharpJac i₁ g ∧ sharpJac i₁ g ≤ 5 / 4 := by
  have h := sharp_coord_bounds i₁ hg
  unfold sharpJac
  constructor <;> linarith [h.1, h.2]

private theorem sharp_jac_ne_zero (i₁ : Fin d) (g : Vec d) (hg : euclideanNorm g ≤ 1 / 4) :
    sharpJac i₁ g ≠ 0 := by
  have h : (0 : ℝ) < sharpJac i₁ g := by linarith [(sharpJac_bounds i₁ g hg).1]
  exact h.ne'

private theorem sharp_dot_mul_dot_le (ξ g : Vec d) :
    dot ξ g * dot ξ g ≤ euclideanSq g * euclideanSq ξ := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ g ξ
  have e1 : dot ξ g = ∑ i, g i * ξ i := by
    unfold dot
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have e2 : euclideanSq g = ∑ i, g i ^ 2 := by
    unfold euclideanSq dot
    exact Finset.sum_congr rfl fun i _ => (sq (g i)).symm
  have e3 : euclideanSq ξ = ∑ i, ξ i ^ 2 := by
    unfold euclideanSq dot
    exact Finset.sum_congr rfl fun i _ => (sq (ξ i)).symm
  rw [e1, e2, e3, ← sq]
  exact h

private theorem sharp_dot_sub_smul (ξ g : Vec d) (c : ℝ) :
    dot (ξ - c • g) (ξ - c • g) = dot ξ ξ - 2 * c * dot ξ g + c ^ 2 * dot g g := by
  simp only [sharp_dot_eq, sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, dotProduct_comm g ξ]
  ring

/-! ### Rank-one algebra -/

private theorem sharp_vecMulVec_mul_same (u v w : Vec d) :
    Matrix.vecMulVec u v * Matrix.vecMulVec u w = dotProduct v u • Matrix.vecMulVec u w := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul,
    dotProduct, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

private theorem sharp_vecMulVec_mulVec (u v w : Vec d) :
    Matrix.vecMulVec u v *ᵥ w = dotProduct v w • u := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

private theorem sharp_one_add_mul_one_sub_smul (P : Mat d) (k : ℝ) (hk : 1 + k ≠ 0)
    (hPP : P * P = k • P) : (1 + P) * (1 - (1 + k)⁻¹ • P) = 1 := by
  have hs : (1 + k)⁻¹ * (1 + k) = 1 := inv_mul_cancel₀ hk
  have h2 : (1 : ℝ) - (1 + k)⁻¹ - (1 + k)⁻¹ * k = 0 := by
    linear_combination (-1 : ℝ) * hs
  have h1 : (1 + P) * (1 - (1 + k)⁻¹ • P) =
      1 + (1 - (1 + k)⁻¹ - (1 + k)⁻¹ * k) • P := by
    rw [add_mul, one_mul, mul_sub, mul_one, Matrix.mul_smul, hPP, smul_smul]
    module
  rw [h1, h2, zero_smul, add_zero]

/-! ### Step 1: determinant and inverse -/

/-- Step 1 of `sharp.example`: the determinant of `J g` is `jac g`. -/
theorem sharpJ_det (i₁ : Fin d) (g : Vec d) : (sharpJ i₁ g).det = sharpJac i₁ g := by
  unfold sharpJ sharpJac
  rw [Matrix.vecMulVec_eq Unit, Matrix.det_one_add_replicateCol_mul_replicateRow,
    sharp_dotProduct_unitVector]

private theorem sharp_J_inv (i₁ : Fin d) (g : Vec d) (hk : sharpJac i₁ g ≠ 0) :
    (sharpJ i₁ g)⁻¹ = 1 - (sharpJac i₁ g)⁻¹ • Matrix.vecMulVec (unitVector i₁) g := by
  have hPP : Matrix.vecMulVec (unitVector i₁) g * Matrix.vecMulVec (unitVector i₁) g =
      g i₁ • Matrix.vecMulVec (unitVector i₁) g := by
    rw [sharp_vecMulVec_mul_same, sharp_dotProduct_unitVector]
  unfold sharpJ
  unfold sharpJac at hk ⊢
  apply Matrix.inv_eq_right_inv
  exact sharp_one_add_mul_one_sub_smul _ (g i₁) hk hPP

/-- Step 1 of `sharp.example`: `(J g)⁻¹ = I - (jac g)⁻¹ e ⊗ g`, checked by multiplication. -/
theorem sharpJ_inv (i₁ : Fin d) (g : Vec d) (hg : euclideanNorm g ≤ 1 / 4) :
    (sharpJ i₁ g)⁻¹ = 1 - (sharpJac i₁ g)⁻¹ • Matrix.vecMulVec (unitVector i₁) g :=
  sharp_J_inv i₁ g (sharp_jac_ne_zero i₁ g hg)

private theorem sharp_transpose_J_inv (i₁ : Fin d) (g : Vec d) (hk : sharpJac i₁ g ≠ 0) :
    ((sharpJ i₁ g)⁻¹)ᵀ = 1 - (sharpJac i₁ g)⁻¹ • Matrix.vecMulVec g (unitVector i₁) := by
  rw [sharp_J_inv i₁ g hk, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul,
    Matrix.transpose_vecMulVec]

/-- The transposed inverse acts by `(J g)⁻ᵀ ξ = ξ - (jac g)⁻¹ ξ_{i₁} g`. -/
private theorem sharp_transpose_J_inv_mulVec (i₁ : Fin d) (g ξ : Vec d)
    (hk : sharpJac i₁ g ≠ 0) :
    ((sharpJ i₁ g)⁻¹)ᵀ *ᵥ ξ = ξ - ((sharpJac i₁ g)⁻¹ * ξ i₁) • g := by
  rw [sharp_transpose_J_inv i₁ g hk, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    sharp_vecMulVec_mulVec, sharp_unitVector_dotProduct, smul_smul]

private theorem sharp_transpose_J_inv_mulVec_unitVector (i₁ : Fin d) (g : Vec d)
    (hk : sharpJac i₁ g ≠ 0) :
    ((sharpJ i₁ g)⁻¹)ᵀ *ᵥ unitVector i₁ = unitVector i₁ - (sharpJac i₁ g)⁻¹ • g := by
  have h1 : unitVector i₁ i₁ = 1 := by simp [unitVector]
  rw [sharp_transpose_J_inv_mulVec i₁ g (unitVector i₁) hk, h1, mul_one]

private theorem sharp_transpose_J_inv_mulVec_add (i₁ : Fin d) (g : Vec d)
    (hk : sharpJac i₁ g ≠ 0) :
    ((sharpJ i₁ g)⁻¹)ᵀ *ᵥ (unitVector i₁ + g) = unitVector i₁ := by
  have h1 : (unitVector i₁ + g) i₁ = sharpJac i₁ g := by
    simp [unitVector, sharpJac]
  rw [sharp_transpose_J_inv_mulVec i₁ g (unitVector i₁ + g) hk, h1, inv_mul_cancel₀ hk,
    one_smul]
  abel

private theorem sharp_J_inv_mulVec_unitVector (i₁ : Fin d) (g : Vec d)
    (hk : sharpJac i₁ g ≠ 0) :
    (sharpJ i₁ g)⁻¹ *ᵥ unitVector i₁ = (sharpJac i₁ g)⁻¹ • unitVector i₁ := by
  have hs1 : (sharpJac i₁ g)⁻¹ = 1 - (sharpJac i₁ g)⁻¹ * g i₁ := by
    have h := mul_inv_cancel₀ hk
    unfold sharpJac at h ⊢
    linear_combination h
  rw [sharp_J_inv i₁ g hk, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    sharp_vecMulVec_mulVec, sharp_dotProduct_unitVector, smul_smul]
  calc unitVector i₁ - ((sharpJac i₁ g)⁻¹ * g i₁) • unitVector i₁
      = (1 - (sharpJac i₁ g)⁻¹ * g i₁) • unitVector i₁ := by rw [sub_smul, one_smul]
    _ = (sharpJac i₁ g)⁻¹ • unitVector i₁ := by rw [← hs1]

private theorem sharp_J_inv_mulVec_self (i₁ : Fin d) (g : Vec d) (hk : sharpJac i₁ g ≠ 0) :
    (sharpJ i₁ g)⁻¹ *ᵥ g = g - (sharpJac i₁ g)⁻¹ • (euclideanSq g • unitVector i₁) := by
  rw [sharp_J_inv i₁ g hk, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    sharp_vecMulVec_mulVec, sharp_euclideanSq_eq]

/-! ### Step 2: symmetry and the harmonic identity -/

/-- Step 2 of `sharp.example`: the coefficient is symmetric. -/
theorem sharpCoeff_transpose (i₁ : Fin d) (g : Vec d) :
    (sharpCoeff i₁ g).transpose = sharpCoeff i₁ g := by
  unfold sharpCoeff
  rw [Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_transpose]

private theorem sharp_coeff_identity (j s G : ℝ) (e g : Vec d) (hjs : j * s = 1) :
    j • (s • e - s • (g - s • (G • e))) = (1 + s * G) • e - g := by
  have h2 : j • (s • e - s • (g - s • (G • e))) =
      (j * s) • e - (j * s) • g + (j * s * s * G) • e := by
    module
  rw [h2, hjs]
  module

private theorem sharp_coeff_mulVec_unitVector (i₁ : Fin d) (g : Vec d)
    (hk : sharpJac i₁ g ≠ 0) :
    (sharpCoeff i₁ g).mulVec (unitVector i₁) =
      (1 + (sharpJac i₁ g)⁻¹ * euclideanSq g) • unitVector i₁ - g := by
  unfold sharpCoeff
  rw [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
    sharp_transpose_J_inv_mulVec_unitVector i₁ g hk, Matrix.mulVec_sub, Matrix.mulVec_smul,
    sharp_J_inv_mulVec_unitVector i₁ g hk, sharp_J_inv_mulVec_self i₁ g hk]
  exact sharp_coeff_identity _ _ _ _ _ (mul_inv_cancel₀ hk)

/-- Step 2 of `sharp.example`, `eq.sharp-harmonic`: `a (e + ∇ψ) = e`. -/
theorem sharpCoeff_mulVec_harmonic (i₁ : Fin d) (g : Vec d) (hg : euclideanNorm g ≤ 1 / 4) :
    (sharpCoeff i₁ g).mulVec (unitVector i₁ + g) = unitVector i₁ := by
  have hk := sharp_jac_ne_zero i₁ g hg
  unfold sharpCoeff
  rw [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, sharp_transpose_J_inv_mulVec_add i₁ g hk,
    sharp_J_inv_mulVec_unitVector i₁ g hk, smul_smul, mul_inv_cancel₀ hk, one_smul]

/-! ### Step 4: the entry `a_{i₁ i₁}` and the pairing with `g` -/

/-- Step 4 of `sharp.example`: the diagonal entry `a_{i₁ i₁}`. -/
theorem sharpCoeff_apply_self (i₁ : Fin d) (g : Vec d) (hg : euclideanNorm g ≤ 1 / 4) :
    (sharpCoeff i₁ g) i₁ i₁ = 1 - g i₁ + euclideanSq g / sharpJac i₁ g := by
  have hk := sharp_jac_ne_zero i₁ g hg
  have hM : (sharpCoeff i₁ g).mulVec (unitVector i₁) i₁ = (sharpCoeff i₁ g) i₁ i₁ := by
    have h0 := congrFun (Matrix.mulVec_single_one (sharpCoeff i₁ g) i₁) i₁
    exact h0
  have h := congrFun (sharp_coeff_mulVec_unitVector i₁ g hk) i₁
  rw [hM] at h
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, unitVector, Pi.single_eq_same,
    mul_one] at h
  rw [h]
  ring

/-- Step 4 of `sharp.example`: `dot (a e) g = 1 - a_{i₁ i₁}`, the identity behind `eq.sharp-constant`. -/
theorem sharpCoeff_dot_mulVec_unitVector (i₁ : Fin d) (g : Vec d)
    (hg : euclideanNorm g ≤ 1 / 4) :
    dot ((sharpCoeff i₁ g).mulVec (unitVector i₁)) g = 1 - (sharpCoeff i₁ g) i₁ i₁ := by
  have hk := sharp_jac_ne_zero i₁ g hg
  have hs : (sharpJac i₁ g)⁻¹ * sharpJac i₁ g = 1 := inv_mul_cancel₀ hk
  rw [sharp_coeff_mulVec_unitVector i₁ g hk, sharpCoeff_apply_self i₁ g hg]
  unfold sharpJac at hs ⊢
  rw [sharp_dot_eq, sub_dotProduct, smul_dotProduct, sharp_unitVector_dotProduct, smul_eq_mul,
    ← sharp_euclideanSq_eq]
  linear_combination (euclideanSq g) * hs

/-! ### Step 4: uniform ellipticity -/

/-- Quadratic form of the coefficient: `ξ · a ξ = jac g · |(J g)⁻ᵀ ξ|²`. -/
private theorem sharp_dot_sharpCoeff (i₁ : Fin d) (g ξ : Vec d) :
    dot ξ ((sharpCoeff i₁ g).mulVec ξ) =
      sharpJac i₁ g * dot (((sharpJ i₁ g)⁻¹)ᵀ *ᵥ ξ) (((sharpJ i₁ g)⁻¹)ᵀ *ᵥ ξ) := by
  simp only [sharp_dot_eq]
  unfold sharpCoeff
  rw [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, dotProduct_smul, Matrix.dotProduct_mulVec ξ,
    ← Matrix.mulVec_transpose, smul_eq_mul]

/-- Real estimate behind the ellipticity bounds, with `X = |ξ|²`, `t = ξ_{i₁}`,
`p = ξ · g`, `G = |g|²` and `s = jac⁻¹`. -/
private theorem sharp_quadratic_bounds {X t p G s j : ℝ}
    (hX : 0 ≤ X) (ht : t * t ≤ X) (hp : p * p ≤ G * X) (hG0 : 0 ≤ G) (hG : G ≤ 1 / 16)
    (hs0 : 0 ≤ s) (hs : s ≤ 4 / 3) (hj1 : 3 / 4 ≤ j) (hj2 : j ≤ 5 / 4) :
    1 / 4 * X ≤ j * (X - 2 * (s * t) * p + (s * t) ^ 2 * G) ∧
      j * (X - 2 * (s * t) * p + (s * t) ^ 2 * G) ≤ 20 / 9 * X := by
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = X - 2 * (s * t) * p + (s * t) ^ 2 * G := ⟨_, rfl⟩
  rw [← hQ]
  have hR1 : -2 * t * p ≤ t * t / 4 + 4 * (p * p) := by
    nlinarith [sq_nonneg (t / 2 + 2 * p)]
  have hR2 : 2 * t * p ≤ t * t / 4 + 4 * (p * p) := by
    nlinarith [sq_nonneg (t / 2 - 2 * p)]
  have hGX : G * X ≤ 1 / 16 * X := mul_le_mul_of_nonneg_right hG hX
  have hR : t * t / 4 + 4 * (p * p) ≤ X / 2 := by linarith
  have hsR1 : s * (-2 * t * p) ≤ s * (t * t / 4 + 4 * (p * p)) :=
    mul_le_mul_of_nonneg_left hR1 hs0
  have hsR2 : s * (2 * t * p) ≤ s * (t * t / 4 + 4 * (p * p)) :=
    mul_le_mul_of_nonneg_left hR2 hs0
  have hsR : s * (t * t / 4 + 4 * (p * p)) ≤ s * (X / 2) :=
    mul_le_mul_of_nonneg_left hR hs0
  have hsX : s * X ≤ 4 / 3 * X := mul_le_mul_of_nonneg_right hs hX
  have hsR' : s * (X / 2) ≤ 2 / 3 * X := by linarith
  have hs2 : s * s ≤ 16 / 9 := by nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hs)]
  have hst : (s * t) ^ 2 ≤ 16 / 9 * X := by
    have e1 : (s * t) ^ 2 = s * s * (t * t) := by ring
    have h1 : s * s * (t * t) ≤ 16 / 9 * (t * t) :=
      mul_le_mul_of_nonneg_right hs2 (mul_self_nonneg t)
    rw [e1]
    linarith
  have hstG : (s * t) ^ 2 * G ≤ 1 / 9 * X := by
    have h1 : (s * t) ^ 2 * G ≤ 16 / 9 * X * G := mul_le_mul_of_nonneg_right hst hG0
    linarith
  have hstG0 : 0 ≤ (s * t) ^ 2 * G := mul_nonneg (sq_nonneg _) hG0
  have hQlo : X / 3 ≤ Q := by linarith
  have hQup : Q ≤ 16 / 9 * X := by linarith
  have hQ0 : 0 ≤ Q := by linarith
  have h3 : 3 / 4 * Q ≤ j * Q := mul_le_mul_of_nonneg_right hj1 hQ0
  have h4 : j * Q ≤ 5 / 4 * Q := mul_le_mul_of_nonneg_right hj2 hQ0
  exact ⟨by linarith, by linarith⟩

/-- Step 4 of `sharp.example`: uniform ellipticity of `sharpCoeff g` with the explicit
constants `c₁ = 1/4` and `c₂ = 20/9`, for `|g| ≤ 1/4`. -/
theorem sharpCoeff_uniformlyElliptic (i₁ : Fin d) (g : Vec d) (hg : euclideanNorm g ≤ 1 / 4)
    (ξ : Vec d) :
    1 / 4 * euclideanSq ξ ≤ dot ξ ((sharpCoeff i₁ g).mulVec ξ) ∧
      dot ξ ((sharpCoeff i₁ g).mulVec ξ) ≤ 20 / 9 * euclideanSq ξ := by
  have hk := sharp_jac_ne_zero i₁ g hg
  have hj := sharpJac_bounds i₁ g hg
  have hpos : 0 < sharpJac i₁ g := by linarith [hj.1]
  have hs0 : 0 ≤ (sharpJac i₁ g)⁻¹ := inv_nonneg.mpr hpos.le
  have hsj : sharpJac i₁ g * (sharpJac i₁ g)⁻¹ = 1 := mul_inv_cancel₀ hk
  have hs : (sharpJac i₁ g)⁻¹ ≤ 4 / 3 := by
    nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hj.1)]
  have key := sharp_quadratic_bounds (X := euclideanSq ξ) (t := ξ i₁) (p := dot ξ g)
    (G := euclideanSq g) (s := (sharpJac i₁ g)⁻¹) (j := sharpJac i₁ g)
    (sharp_euclideanSq_nonneg ξ) (sharp_sq_coord_le i₁ ξ) (sharp_dot_mul_dot_le ξ g)
    (sharp_euclideanSq_nonneg g) (sharp_euclideanSq_le_sixteenth hg) hs0 hs hj.1 hj.2
  rw [sharp_dot_sharpCoeff i₁ g ξ, sharp_transpose_J_inv_mulVec i₁ g ξ hk, sharp_dot_sub_smul]
  exact key

end EinsteinRelation.Sharpness
