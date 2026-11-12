import EinsteinRelation.Environment.MatrixNorm
import Mathlib.Data.Fin.VecNotation
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Centering the independent entry of a planar skew matrix

Source: `paper/main.tex:864–875`. The exact factor `sqrt 2` converts
the independent entry into the manuscript's Frobenius norm.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

/-- The Frobenius norm of a planar skew matrix; paper/main.tex:869–875. -/
theorem frobeniusNorm_planar_skew (A : Mat 2) (hA : A.transpose = -A) :
    frobeniusNorm A = Real.sqrt 2 * |A 0 1| := by
  -- From Aᵀ = -A, extract entrywise equalities
  have h_entry (i j : Fin 2) : A j i = -A i j := by
    have h := congrArg (fun M : Mat 2 => M i j) hA
    simpa [Matrix.transpose_apply] using h
  -- Diagonal entries are zero
  have h_diag (i : Fin 2) : A i i = 0 := by
    have h_eq := h_entry i i
    linarith
  -- Compute frobeniusSq explicitly for 2x2
  have h_frobeniusSq : frobeniusSq A = 2 * (A 0 1) ^ 2 := by
    unfold frobeniusSq
    calc
      ∑ i : Fin 2, ∑ j : Fin 2, A i j * A i j
          = (A 0 0 * A 0 0 + A 0 1 * A 0 1) + (A 1 0 * A 1 0 + A 1 1 * A 1 1) := by
        simp [Fin.sum_univ_two]
      _ = (0 * 0 + A 0 1 * A 0 1) + ((-A 0 1) * (-A 0 1) + 0 * 0) := by
        simp [h_diag 0, h_diag 1, h_entry 0 1]
      _ = A 0 1 * A 0 1 + A 0 1 * A 0 1 := by ring
      _ = 2 * (A 0 1) ^ 2 := by ring
  -- Now compute the Frobenius norm
  rw [frobeniusNorm, h_frobeniusSq]
  calc
    Real.sqrt (2 * (A 0 1) ^ 2) = Real.sqrt (2 * ((A 0 1) ^ 2)) := rfl
    _ = Real.sqrt 2 * Real.sqrt ((A 0 1) ^ 2) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    _ = Real.sqrt 2 * |A 0 1| := by rw [Real.sqrt_sq_eq_abs]

/-- Difference of two actual centered scalar fields; paper/main.tex:864–875. -/
theorem centered_pair_subtraction {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (u v w : X → ℝ) (x₀ : X)
    (hu : Integrable (fun x => w x * u x) μ)
    (hv : Integrable (fun x => w x * v x) μ) :
    (u x₀ - ∫ x, w x * u x ∂μ) - (v x₀ - ∫ x, w x * v x ∂μ) =
      (u x₀ - v x₀) - ∫ x, w x * (u x - v x) ∂μ := by
  calc
    (u x₀ - ∫ x, w x * u x ∂μ) - (v x₀ - ∫ x, w x * v x ∂μ)
        = (u x₀ - v x₀) - (∫ x, w x * u x ∂μ - ∫ x, w x * v x ∂μ) := by ring
    _ = (u x₀ - v x₀) - ∫ x, (w x * u x - w x * v x) ∂μ := by
      rw [integral_sub hu hv]
    _ = (u x₀ - v x₀) - ∫ x, w x * (u x - v x) ∂μ := by
      congr
      ext x
      rw [mul_sub]

/-- Kernel centering preserves skewness; paper/main.tex:869–875. -/
theorem transpose_centered_skew {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (S : X → Mat 2) (w : X → ℝ) (x₀ : X)
    (hpoint : (S x₀).transpose = -(S x₀))
    (hS : ∀ᵐ x ∂μ, (S x).transpose = -(S x)) :
    (Matrix.of (fun a b => S x₀ a b - ∫ x, w x * S x a b ∂μ)).transpose =
      -(Matrix.of (fun a b => S x₀ a b - ∫ x, w x * S x a b ∂μ)) := by
  ext a b
  have hp : S x₀ b a = -S x₀ a b := congrArg (fun M : Mat 2 => M a b) hpoint
  have hi : (∫ x, w x * S x b a ∂μ) = -(∫ x, w x * S x a b ∂μ) := by
    calc
      _ = ∫ x, -(w x * S x a b) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hS] with x hx
        have he : S x b a = -S x a b := congrArg (fun M : Mat 2 => M a b) hx
        rw [he, mul_neg]
      _ = _ := integral_neg _
  change S x₀ b a - (∫ x, w x * S x b a ∂μ) =
    -(S x₀ a b - ∫ x, w x * S x a b ∂μ)
  rw [hp, hi]
  ring

end EinsteinRelation.Correctors
