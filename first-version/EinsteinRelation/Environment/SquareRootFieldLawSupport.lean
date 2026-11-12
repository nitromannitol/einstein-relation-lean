import EinsteinRelation.Environment.Basic
import Mathlib.Analysis.Matrix.Order

open Matrix
open scoped MatrixOrder

namespace EinsteinRelation

/-- A symmetric elliptic coefficient matrix is positive semidefinite. -/
theorem elliptic_matrix_posSemidef {d : ℕ} {Λ : ℝ} (hΛ : 1 ≤ Λ)
    {a : Vec d → Mat d} (ha : IsElliptic Λ a) (x : Vec d) :
    (a x).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · change (a x)ᴴ = a x
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    exact (ha x).1
  · intro ξ
    have hquad := (ha x).2 ξ
    have hsquare : 0 ≤ euclideanSq ξ := by
      unfold euclideanSq dot
      apply Finset.sum_nonneg
      intro i hi
      exact mul_self_nonneg (ξ i)
    have hinv : 0 ≤ Λ⁻¹ := inv_nonneg.mpr (by linarith)
    have hnonneg : 0 ≤ Λ⁻¹ * euclideanSq ξ := mul_nonneg hinv hsquare
    have hdot : 0 ≤ dot ξ ((a x).mulVec ξ) := hnonneg.trans hquad.1
    simpa [dot, dotProduct] using hdot

/-- The pinned matrix continuous functional calculus supplies the positive symmetric
square root and its defining product identity on every physical regular field. -/
theorem regularCoefficient_cfcSqrt_spec {d : ℕ} {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (ω : FieldPair d) (hω : IsRegular Λ ω) (x : Vec d) :
    CFC.sqrt (ω.1 x) * CFC.sqrt (ω.1 x) = ω.1 x ∧
      (CFC.sqrt (ω.1 x)).PosSemidef := by
  have hpsd : (ω.1 x).PosSemidef := elliptic_matrix_posSemidef hΛ hω.1 x
  refine ⟨CFC.sqrt_mul_sqrt_self (ω.1 x) hpsd.nonneg, ?_⟩
  exact Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (ω.1 x))

/-- A nonconstant physical regular coefficient field remains nonconstant under
the pointwise CFC square root. This is a consumer on the actual field carrier;
it does not claim field-valued continuity or measurability of that operation. -/
theorem nonconstant_regular_coefficient_cfcSqrt {d : ℕ} {Λ : ℝ}
    (hΛ : 1 ≤ Λ) (ω : FieldPair d) (hω : IsRegular Λ ω)
    (hnc : ∃ x y : Vec d, ω.1 x ≠ ω.1 y) :
    ∃ x y : Vec d, CFC.sqrt (ω.1 x) ≠ CFC.sqrt (ω.1 y) := by
  obtain ⟨x, y, hxy⟩ := hnc
  refine ⟨x, y, ?_⟩
  intro hroot
  apply hxy
  calc
    ω.1 x = CFC.sqrt (ω.1 x) * CFC.sqrt (ω.1 x) :=
      (regularCoefficient_cfcSqrt_spec hΛ ω hω x).1.symm
    _ = CFC.sqrt (ω.1 y) * CFC.sqrt (ω.1 y) := by rw [hroot]
    _ = ω.1 y := (regularCoefficient_cfcSqrt_spec hΛ ω hω y).1

end EinsteinRelation
