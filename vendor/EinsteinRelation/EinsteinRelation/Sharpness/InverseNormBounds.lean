import EinsteinRelation.TimeChange.Pairing
import EinsteinRelation.Sharpness.InverseIdentification
import Mathlib.Data.Real.Sqrt

/-! # Uniform Euclidean bounds for the transposed inverse candidate

`paper/main.tex:1218–1231`. For `euclideanNorm g ≤ 1/4`, the candidate inverse
`B = 1 - j⁻¹ (e₁ ⊗ g)` with `j = 1 + gᵢ ∈ [3/4, 5/4]` acts on the transpose by
`Bᵀ ξ = ξ - j⁻¹ ξᵢ g`. Hence `2/3 |ξ| ≤ |Bᵀ ξ| ≤ 4/3 |ξ|` in the explicit
Euclidean norm. This is the deterministic input for the identity
`ξ · (a ξ) = j |Bᵀ ξ|²` with `a = j B Bᵀ`, which gives numerical ellipticity.

The lower bound `j ≥ 3/4` is derived from the gradient bound, so no separate
nonvanishing hypothesis on the Jacobian is assumed.
-/

namespace EinsteinRelation.Sharpness

open EinsteinRelation.TimeChange (euclideanNorm_add_le euclideanNorm_smul)

/-- Each coordinate is bounded by the explicit Euclidean norm. -/
private theorem inverseNorm_abs_coord_le_euclideanNorm {d : ℕ} (i : Fin d) (x : Vec d) :
    |x i| ≤ euclideanNorm x := by
  unfold euclideanNorm
  apply Real.abs_le_sqrt
  unfold euclideanSq dot
  rw [pow_two]
  exact Finset.single_le_sum (f := fun j => x j * x j)
    (fun j _ => mul_self_nonneg (x j)) (Finset.mem_univ i)

/-- The explicit Euclidean norm is nonnegative. -/
private theorem inverseNorm_euclideanNorm_nonneg {d : ℕ} (x : Vec d) :
    0 ≤ euclideanNorm x := by
  unfold euclideanNorm
  exact Real.sqrt_nonneg _

/-- Transpose of an outer product: `(u ⊗ v)ᵀ = v ⊗ u`. -/
private theorem inverseNorm_outer_transpose {d : ℕ} (u v : Vec d) :
    (outer u v).transpose = outer v u := by
  ext k l
  simp only [Matrix.transpose_apply, outer]
  ring

/-- Action of an outer product on a vector: `(u ⊗ v) w = (v · w) u`. -/
private theorem inverseNorm_outer_mulVec {d : ℕ} (u v w : Vec d) :
    (outer u v).mulVec w = dot v w • u := by
  funext k
  simp only [Matrix.mulVec, dotProduct, outer, dot, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun m _ => by ring

/-- The unit vector pairs with `x` to give the `i`-th coordinate of `x`. -/
private theorem inverseNorm_dot_unitVector {d : ℕ} (i : Fin d) (x : Vec d) :
    dot (unitVector i) x = x i := by
  simp [dot, unitVector, Pi.single_apply, ite_mul]

/-- The transpose of the candidate inverse is `1 - j⁻¹ (g ⊗ e₁)`. -/
private theorem inverseNorm_transpose_inverseCandidate {d : ℕ} (i : Fin d) (g : Vec d) :
    (inverseCandidate i g).transpose =
      1 - (jacobianFactor i g)⁻¹ • outer g (unitVector i) := by
  unfold inverseCandidate
  rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul,
    inverseNorm_outer_transpose]

/-- Explicit action of the transposed candidate: `Bᵀ ξ = ξ + (-(j⁻¹ ξᵢ)) • g`. -/
private theorem inverseNorm_transpose_mulVec {d : ℕ} (i : Fin d) (g ξ : Vec d) :
    (inverseCandidate i g).transpose.mulVec ξ =
      ξ + (-((jacobianFactor i g)⁻¹ * ξ i)) • g := by
  rw [inverseNorm_transpose_inverseCandidate, Matrix.sub_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec, inverseNorm_outer_mulVec, inverseNorm_dot_unitVector, smul_smul,
    neg_smul, sub_eq_add_neg]

/-- Under the gradient bound, the perturbation `j⁻¹ ξᵢ g` has norm at most `|ξ| / 3`.
The factor `j⁻¹` lies in `[0, 4/3]` because `j ≥ 3/4` follows from `‖g‖ ≤ 1/4`. -/
private theorem inverseNorm_perturbation_le {d : ℕ} (i : Fin d) (g ξ : Vec d)
    (hg : euclideanNorm g ≤ (1 / 4 : ℝ)) :
    |(jacobianFactor i g)⁻¹ * ξ i| * euclideanNorm g ≤ (1 / 3 : ℝ) * euclideanNorm ξ := by
  obtain ⟨hj₁, _⟩ := jacobianFactor_bounds i g hg
  have hjpos : 0 < jacobianFactor i g := by linarith
  have hs₀ : 0 ≤ (jacobianFactor i g)⁻¹ := inv_nonneg.mpr hjpos.le
  have hsj : (jacobianFactor i g)⁻¹ * jacobianFactor i g = 1 := inv_mul_cancel₀ hjpos.ne'
  have hsle : (jacobianFactor i g)⁻¹ ≤ 4 / 3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hj₁) hs₀]
  have hcoord : |ξ i| ≤ euclideanNorm ξ := inverseNorm_abs_coord_le_euclideanNorm i ξ
  have hgnn : 0 ≤ euclideanNorm g := inverseNorm_euclideanNorm_nonneg g
  have hξnn : 0 ≤ euclideanNorm ξ := inverseNorm_euclideanNorm_nonneg ξ
  rw [abs_mul, abs_of_nonneg hs₀]
  have h₁ : (jacobianFactor i g)⁻¹ * |ξ i| ≤ (4 / 3 : ℝ) * euclideanNorm ξ :=
    mul_le_mul hsle hcoord (abs_nonneg _) (by norm_num)
  have h₂ : (jacobianFactor i g)⁻¹ * |ξ i| * euclideanNorm g ≤
      (4 / 3 : ℝ) * euclideanNorm ξ * euclideanNorm g :=
    mul_le_mul_of_nonneg_right h₁ hgnn
  have h₃ : (4 / 3 : ℝ) * euclideanNorm ξ * euclideanNorm g ≤
      (4 / 3 : ℝ) * euclideanNorm ξ * (1 / 4) :=
    mul_le_mul_of_nonneg_left hg (mul_nonneg (by norm_num) hξnn)
  linarith

/-- Uniform Euclidean bounds for the transposed inverse candidate under the gradient
bound `‖∇ψ‖ ≤ 1/4`. Source: `paper/main.tex:1218–1231`. -/
theorem inverseCandidate_transpose_norm_bounds {d : ℕ} (i : Fin d) (g ξ : Vec d)
    (hg : euclideanNorm g ≤ (1 / 4 : ℝ)) :
    (2 / 3 : ℝ) * euclideanNorm ξ ≤ euclideanNorm ((inverseCandidate i g).transpose.mulVec ξ) ∧
    euclideanNorm ((inverseCandidate i g).transpose.mulVec ξ) ≤ (4 / 3 : ℝ) * euclideanNorm ξ := by
  have hq := inverseNorm_perturbation_le i g ξ hg
  rw [inverseNorm_transpose_mulVec]
  have hsum : ξ = (ξ + (-((jacobianFactor i g)⁻¹ * ξ i)) • g) +
      ((jacobianFactor i g)⁻¹ * ξ i) • g := by
    rw [add_assoc, ← add_smul, neg_add_cancel, zero_smul, add_zero]
  have hup := euclideanNorm_add_le ξ ((-((jacobianFactor i g)⁻¹ * ξ i)) • g)
  have hlow : euclideanNorm ξ ≤ euclideanNorm (ξ + (-((jacobianFactor i g)⁻¹ * ξ i)) • g) +
      euclideanNorm (((jacobianFactor i g)⁻¹ * ξ i) • g) :=
    (congrArg euclideanNorm hsum).trans_le (euclideanNorm_add_le _ _)
  rw [euclideanNorm_smul, abs_neg] at hup
  rw [euclideanNorm_smul] at hlow
  constructor <;> linarith

end EinsteinRelation.Sharpness
