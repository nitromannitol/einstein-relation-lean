import EinsteinRelation.Sharpness.InverseNormBounds
import EinsteinRelation.Sharpness.EnergyForm
import EinsteinRelation.Sharpness.Fields
import EinsteinRelation.Sharpness.Energy
import EinsteinRelation.TimeChange.Pairing
import Mathlib.Tactic.Linarith

/-! # Uniform numerical ellipticity of the sharpness coefficients

`paper/main.tex:1218–1231`. For `euclideanNorm g ≤ 1/4`, the coefficient `a = j B Bᵀ` with
`j = 1 + gᵢ ∈ [3/4, 5/4]` and `B = inverseCandidate i g` satisfies `ξ · (a ξ) = j |Bᵀ ξ|²`
(`coefficient_quadratic_form`). The transposed candidate obeys `2/3 |ξ| ≤ |Bᵀ ξ| ≤ 4/3 |ξ|`
(`inverseCandidate_transpose_norm_bounds`), so `1/3 |ξ|² ≤ ξ · (a ξ) ≤ 20/9 |ξ|²`.

For the physical coefficient `μ⁻¹ a`, the clock density bounds `3/4 ≤ μ ≤ 5/4` give
`4/5 ≤ μ⁻¹ ≤ 4/3`, hence `4/15 |ξ|² ≤ ξ · (μ⁻¹ a ξ) ≤ 80/27 |ξ|²`.

All norms are the explicit Euclidean expressions `euclideanNorm`, `euclideanSq`, and `dot`.
The constants are deterministic internal bounds. Lipschitz regularity is not addressed here.
-/

namespace EinsteinRelation.Sharpness

open EinsteinRelation.TimeChange (euclideanSq_eq_sq_euclideanNorm)

/-- Scalar form of the two-sided bound, with `m = |ξ|`, `n = |Bᵀ ξ|`, and `j = 1 + gᵢ`. -/
private theorem coefficient_scalar_bounds (j m n : ℝ)
    (hj₁ : (3 / 4 : ℝ) ≤ j) (hj₂ : j ≤ (5 / 4 : ℝ)) (hm : 0 ≤ m)
    (hn₁ : (2 / 3 : ℝ) * m ≤ n) (hn₂ : n ≤ (4 / 3 : ℝ) * m) :
    (1 / 3 : ℝ) * m ^ 2 ≤ j * n ^ 2 ∧ j * n ^ 2 ≤ (20 / 9 : ℝ) * m ^ 2 := by
  have hn0 : 0 ≤ n := by linarith
  have hlo : (2 / 3 : ℝ) * m * ((2 / 3 : ℝ) * m) ≤ n * n :=
    mul_le_mul hn₁ hn₁ (by linarith) hn0
  have hhi : n * n ≤ (4 / 3 : ℝ) * m * ((4 / 3 : ℝ) * m) :=
    mul_le_mul hn₂ hn₂ hn0 (by linarith)
  have hsq : (0 : ℝ) ≤ n ^ 2 := sq_nonneg n
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right hj₁ hsq]
  · nlinarith [mul_le_mul_of_nonneg_right hj₂ hsq]

/-- The coefficient quadratic form lies between `1/3 |ξ|²` and `20/9 |ξ|²` under the
gradient bound. Source: `paper/main.tex:1218–1231`. -/
theorem coefficient_quadratic_bounds {d : ℕ} (i : Fin d) (g ξ : Vec d)
    (hg : euclideanNorm g ≤ (1 / 4 : ℝ)) :
    (1 / 3 : ℝ) * euclideanSq ξ ≤ dot ξ ((coefficient i g).mulVec ξ) ∧
    dot ξ ((coefficient i g).mulVec ξ) ≤ (20 / 9 : ℝ) * euclideanSq ξ := by
  obtain ⟨hj₁, hj₂⟩ := jacobianFactor_bounds i g hg
  obtain ⟨hn₁, hn₂⟩ := inverseCandidate_transpose_norm_bounds i g ξ hg
  have hm : 0 ≤ euclideanNorm ξ := by
    unfold euclideanNorm
    exact Real.sqrt_nonneg _
  rw [coefficient_quadratic_form, euclideanSq_eq_sq_euclideanNorm ξ,
    euclideanSq_eq_sq_euclideanNorm ((inverseCandidate i g).transpose.mulVec ξ)]
  exact coefficient_scalar_bounds _ _ _ hj₁ hj₂ hm hn₁ hn₂

/-- Scalar multiples pass through the coordinate scalar product. -/
private theorem ellipticity_dot_smul_right {d : ℕ} (c : ℝ) (x y : Vec d) :
    dot x (c • y) = c * dot x y := by
  unfold dot
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- The sharpness coefficient is symmetric and uniformly elliptic with constant `3`
under the gradient bound. Source: `paper/main.tex:1218–1231`. -/
theorem coefficientField_isElliptic {d : ℕ} (i : Fin d) (ψ : Vec d → ℝ)
    (hg : ∀ x, euclideanNorm (gradient ψ x) ≤ (1 / 4 : ℝ)) :
    IsElliptic 3 (coefficientField i ψ) := by
  intro x
  refine ⟨?_, fun ξ => ?_⟩
  · unfold coefficientField
    exact coefficient_transpose i (gradient ψ x)
  · obtain ⟨hlo, hhi⟩ := coefficient_quadratic_bounds i (gradient ψ x) ξ (hg x)
    have hs : 0 ≤ euclideanSq ξ := euclideanSq_nonneg ξ
    have h3 : (3 : ℝ)⁻¹ = 1 / 3 := by norm_num
    unfold coefficientField
    rw [h3]
    exact ⟨hlo, by linarith⟩

/-- The physical coefficient `μ⁻¹ a` is symmetric and uniformly elliptic with constant `4`
under the gradient and clock-density bounds. Source: `paper/main.tex:1218–1231`. -/
theorem physicalCoefficientField_isElliptic {d : ℕ} (i : Fin d) (δ : ℝ) (ψ : Vec d → ℝ)
    (hg : ∀ x, euclideanNorm (gradient ψ x) ≤ (1 / 4 : ℝ))
    (hμ : ∀ x, (3 / 4 : ℝ) ≤ densityField i δ ψ x ∧ densityField i δ ψ x ≤ (5 / 4 : ℝ)) :
    IsElliptic 4 (physicalCoefficientField i δ ψ) := by
  intro x
  obtain ⟨hμ₁, hμ₂⟩ := hμ x
  have hμpos : 0 < densityField i δ ψ x := by linarith
  have hu0 : 0 ≤ (densityField i δ ψ x)⁻¹ := inv_nonneg.mpr hμpos.le
  have hmul : densityField i δ ψ x * (densityField i δ ψ x)⁻¹ = 1 :=
    mul_inv_cancel₀ hμpos.ne'
  have hu₁ : (4 / 5 : ℝ) ≤ (densityField i δ ψ x)⁻¹ := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hμ₂) hu0]
  have hu₂ : (densityField i δ ψ x)⁻¹ ≤ (4 / 3 : ℝ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hμ₁) hu0]
  refine ⟨?_, fun ξ => ?_⟩
  · unfold physicalCoefficientField coefficientField
    rw [Matrix.transpose_smul, coefficient_transpose]
  · obtain ⟨hlo, hhi⟩ := coefficient_quadratic_bounds i (gradient ψ x) ξ (hg x)
    have hs : 0 ≤ euclideanSq ξ := euclideanSq_nonneg ξ
    have hEq : dot ξ ((physicalCoefficientField i δ ψ x).mulVec ξ) =
        (densityField i δ ψ x)⁻¹ * dot ξ ((coefficient i (gradient ψ x)).mulVec ξ) := by
      unfold physicalCoefficientField coefficientField
      rw [Matrix.smul_mulVec, ellipticity_dot_smul_right]
    have hE0 : 0 ≤ dot ξ ((coefficient i (gradient ψ x)).mulVec ξ) := by linarith
    have hlow := mul_le_mul_of_nonneg_right hu₁ hE0
    have hhigh := mul_le_mul_of_nonneg_right hu₂ hE0
    have h4 : (4 : ℝ)⁻¹ = 1 / 4 := by norm_num
    rw [hEq, h4]
    constructor <;> linarith

end EinsteinRelation.Sharpness
