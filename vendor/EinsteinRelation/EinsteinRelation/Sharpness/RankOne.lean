import EinsteinRelation.Sharpness.MatrixDefs

/-! # Rank-one inverse and coefficient identities for the sharpness map

Finite-dimensional algebra for `paper/main.tex`: the Jacobian `J = I + e₁ ⊗ ∇ψ` and its
determinant (`eq.sharp-map`, lines 1218–1223), the harmonic identity `a (e₁ + ∇ψ) = e₁`
(`eq.sharp-harmonic`, lines 1233–1235), and the diagonal entry `a₁₁` used in Step 4 (lines
1257–1259). Here `i` is the coordinate direction `e₁` and `g` stands for `∇ψ`.

All identities are exact algebra over the Euclidean sum of squares `euclideanSq`. No analytic
input is used. The identification of `inverseCandidate` with the true Matrix inverse is not
proved here; it is a follow-up task.
-/

namespace EinsteinRelation.Sharpness

/-- Transpose of an outer product: `(u ⊗ v)ᵀ = v ⊗ u`. -/
private theorem outer_transpose {d : ℕ} (u v : Vec d) :
    (outer u v).transpose = outer v u := by
  ext k l
  simp only [Matrix.transpose_apply, outer]
  ring

/-- Product of outer products: `(u ⊗ v)(w ⊗ x) = (v · w) (u ⊗ x)`. -/
private theorem outer_mul_outer {d : ℕ} (u v w x : Vec d) :
    outer u v * outer w x = dot v w • outer u x := by
  ext k l
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, outer, dot, Finset.sum_mul]
  exact Finset.sum_congr rfl fun m _ => by ring

/-- Action of an outer product on a vector: `(u ⊗ v) w = (v · w) u`. -/
private theorem outer_mulVec {d : ℕ} (u v w : Vec d) :
    (outer u v).mulVec w = dot v w • u := by
  funext k
  simp only [Matrix.mulVec, dotProduct, outer, dot, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun m _ => by ring

/-- The inner product of `g` with the `i`-th unit vector is `gᵢ`. -/
private theorem dot_unitVector_right {d : ℕ} (i : Fin d) (g : Vec d) :
    dot g (unitVector i) = g i := by
  simp [dot, unitVector, Pi.single_apply]

/-- The unit vector has squared Euclidean norm one. -/
private theorem dot_unitVector_self {d : ℕ} (i : Fin d) :
    dot (unitVector i) (unitVector i) = 1 := by
  rw [dot_unitVector_right]
  simp [unitVector]

/-- For `e = unitVector i`, `(e ⊗ g)² = gᵢ (e ⊗ g)`. -/
private theorem outer_unit_mul_self {d : ℕ} (i : Fin d) (g : Vec d) :
    outer (unitVector i) g * outer (unitVector i) g = g i • outer (unitVector i) g := by
  rw [outer_mul_outer, dot_unitVector_right]

/-- Rank-one core: if `E² = cE` and `s (1 + c) = 1`, then `(1 + E)(1 - sE) = 1` and
`(1 - sE)(1 + E) = 1`. This is the algebra behind `J⁻¹ = I - j⁻¹ e₁ ⊗ ∇ψ`. -/
private theorem one_add_mul_one_sub_smul_eq_one {d : ℕ} (E : Mat d) (c s : ℝ)
    (hE : E * E = c • E) (hs : s * (1 + c) = 1) :
    (1 + E) * (1 - s • E) = 1 ∧ (1 - s • E) * (1 + E) = 1 := by
  have h0 : 1 - s - s * c = 0 := by linear_combination (-1 : ℝ) * hs
  have hA : (1 + E) * (1 - s • E) = 1 + (1 - s - s * c) • E := by
    rw [add_mul, one_mul, mul_sub, mul_one, mul_smul_comm, hE, smul_smul, sub_smul,
      sub_smul, one_smul]
    abel
  have hB : (1 - s • E) * (1 + E) = 1 + (1 - s - s * c) • E := by
    rw [sub_mul, one_mul, smul_mul_assoc, mul_add, mul_one, hE, smul_add, smul_smul,
      sub_smul, sub_smul, one_smul]
    abel
  rw [h0, zero_smul, add_zero] at hA hB
  exact ⟨hA, hB⟩

/-- Expanded form of `B Bᵀ` for the candidate inverse `B = 1 - s (e ⊗ g)`, where
`s = (1 + gᵢ)⁻¹`, `e = unitVector i`. -/
private theorem inverseCandidate_mul_transpose {d : ℕ} (i : Fin d) (g : Vec d) :
    inverseCandidate i g * (inverseCandidate i g).transpose =
      1 - (jacobianFactor i g)⁻¹ • outer (unitVector i) g
        - (jacobianFactor i g)⁻¹ • outer g (unitVector i)
        + ((jacobianFactor i g)⁻¹ * ((jacobianFactor i g)⁻¹ * dot g g)) •
            outer (unitVector i) (unitVector i) := by
  unfold inverseCandidate
  rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul, outer_transpose]
  simp only [sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_sub,
    outer_mul_outer, smul_smul]
  abel

/-- The Jacobian `I + e ⊗ g` has inverse `I - (1 + gᵢ)⁻¹ (e ⊗ g)` whenever `1 + gᵢ ≠ 0`.
Source: `paper/main.tex`, `eq.sharp-map`, lines 1218–1223. -/
theorem jacobian_mul_inverseCandidate {d : ℕ} (i : Fin d) (g : Vec d)
    (hj : jacobianFactor i g ≠ 0) : jacobian i g * inverseCandidate i g = 1 := by
  have hs : (jacobianFactor i g)⁻¹ * (1 + g i) = 1 := inv_mul_cancel₀ hj
  unfold jacobian inverseCandidate
  exact (one_add_mul_one_sub_smul_eq_one (outer (unitVector i) g) (g i)
    (jacobianFactor i g)⁻¹ (outer_unit_mul_self i g) hs).1

/-- The candidate inverse is a two-sided inverse of the Jacobian when `1 + gᵢ ≠ 0`.
Source: `paper/main.tex`, `eq.sharp-map`, lines 1218–1223. -/
theorem inverseCandidate_mul_jacobian {d : ℕ} (i : Fin d) (g : Vec d)
    (hj : jacobianFactor i g ≠ 0) : inverseCandidate i g * jacobian i g = 1 := by
  have hs : (jacobianFactor i g)⁻¹ * (1 + g i) = 1 := inv_mul_cancel₀ hj
  unfold jacobian inverseCandidate
  exact (one_add_mul_one_sub_smul_eq_one (outer (unitVector i) g) (g i)
    (jacobianFactor i g)⁻¹ (outer_unit_mul_self i g) hs).2

/-- The coefficient `a = j B Bᵀ` satisfies `a (e₁ + ∇ψ) = e₁` when `1 + gᵢ ≠ 0`.
Source: `paper/main.tex`, `eq.sharp-harmonic`, lines 1233–1235. -/
theorem coefficient_mulVec {d : ℕ} (i : Fin d) (g : Vec d)
    (hj : jacobianFactor i g ≠ 0) :
    (coefficient i g).mulVec (unitVector i + g) = unitVector i := by
  have hJB : jacobian i g * inverseCandidate i g = 1 := jacobian_mul_inverseCandidate i g hj
  have hT : (jacobian i g).transpose.mulVec (unitVector i) = unitVector i + g := by
    unfold jacobian
    rw [Matrix.transpose_add, Matrix.transpose_one, outer_transpose, Matrix.add_mulVec,
      Matrix.one_mulVec, outer_mulVec, dot_unitVector_self, one_smul]
  have hBT : (inverseCandidate i g).transpose * (jacobian i g).transpose = 1 := by
    rw [← Matrix.transpose_mul, hJB, Matrix.transpose_one]
  have hs : (1 + g i)⁻¹ * (1 + g i) = 1 := inv_mul_cancel₀ hj
  unfold coefficient
  rw [← hT, Matrix.smul_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, hBT, Matrix.mul_one]
  unfold inverseCandidate
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, outer_mulVec,
    dot_unitVector_right]
  funext k
  simp only [jacobianFactor, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  linear_combination (-(g i * unitVector i k)) * hs

/-- Diagonal entry of the coefficient: `a₁₁ = 1 - g₁ + |g|² / (1 + g₁)`, with `g₁ = ∂₁ψ`.
Source: `paper/main.tex`, Step 4 of Proposition `sharp.example`, lines 1257–1259. -/
theorem coefficient_diagonal {d : ℕ} (i : Fin d) (g : Vec d)
    (hj : jacobianFactor i g ≠ 0) :
    coefficient i g i i = 1 - g i + euclideanSq g / (1 + g i) := by
  have hs : (1 + g i)⁻¹ * (1 + g i) = 1 := inv_mul_cancel₀ hj
  have he : unitVector i i = 1 := by simp [unitVector]
  unfold coefficient
  rw [inverseCandidate_mul_transpose]
  simp only [jacobianFactor, euclideanSq, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply,
    Matrix.one_apply_eq, outer, smul_eq_mul, he, mul_one, one_mul]
  linear_combination ((1 + g i)⁻¹ * dot g g - 2 * g i) * hs

/-- The coefficient is symmetric, with no assumption on the Jacobian. -/
theorem coefficient_transpose {d : ℕ} (i : Fin d) (g : Vec d) :
    (coefficient i g).transpose = coefficient i g := by
  unfold coefficient
  rw [Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_transpose]

end EinsteinRelation.Sharpness
