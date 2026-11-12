import Mathlib
import EinsteinRelation.Environment.Basic
open MeasureTheory Filter
open scoped Topology ENNReal
namespace EinsteinRelation.Correctors

/-! # Coercivity of the inverse of a coercive matrix

A matrix whose Euclidean quadratic form is coercive is invertible. Its inverse
is coercive with constant `lam / Λ²`, where `Λ²` bounds the squared Frobenius
norm. Symmetry is not assumed: the proof uses only the quadratic form and the
row Cauchy–Schwarz bound `|M η|² ≤ (∑ᵢⱼ |Mᵢⱼ|²) |η|²`.
-/

private theorem coercInv_euclideanSq_nonneg {d : ℕ} (x : Vec d) : 0 ≤ euclideanSq x := by
  unfold euclideanSq dot
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

private theorem coercInv_euclideanSq_pos {d : ℕ} {x : Vec d} (hx : x ≠ 0) :
    0 < euclideanSq x := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  have hi' : x i ≠ 0 := hi
  have hnn : ∀ j ∈ (Finset.univ : Finset (Fin d)), 0 ≤ x j * x j :=
    fun j _ => mul_self_nonneg (x j)
  have hle : x i * x i ≤ ∑ j, x j * x j := Finset.single_le_sum hnn (Finset.mem_univ i)
  have hpos : 0 < x i * x i := mul_self_pos.mpr hi'
  unfold euclideanSq dot
  linarith

private theorem coercInv_dot_comm {d : ℕ} (x y : Vec d) : dot x y = dot y x := by
  unfold dot
  exact Finset.sum_congr rfl fun i _ => mul_comm (x i) (y i)

/-- The `i`-th coordinate of `M η` is bounded by the row norm of `M` times `|η|`. -/
private theorem coercInv_mulVec_row_sq_le {d : ℕ} (M : Mat d) (η : Vec d) (i : Fin d) :
    (M.mulVec η i) ^ 2 ≤ (∑ j, |M i j| ^ 2) * euclideanSq η := by
  have hcs : (∑ j, M i j * η j) ^ 2 ≤ (∑ j, M i j ^ 2) * ∑ j, η j ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => M i j) η
  have hrow : (∑ j, |M i j| ^ 2) = ∑ j, M i j ^ 2 :=
    Finset.sum_congr rfl fun j _ => sq_abs (M i j)
  have hsq : euclideanSq η = ∑ j, η j ^ 2 := by
    unfold euclideanSq dot
    exact Finset.sum_congr rfl fun j _ => by ring
  have hmv : M.mulVec η i = ∑ j, M i j * η j := rfl
  rw [hrow, hsq, hmv]
  exact hcs

/-- Euclidean size of `M η` is bounded by the squared Frobenius norm times `|η|²`. -/
private theorem coercInv_euclideanSq_mulVec_le {d : ℕ} (M : Mat d) (η : Vec d) :
    euclideanSq (M.mulVec η) ≤ (∑ i, ∑ j, |M i j| ^ 2) * euclideanSq η := by
  have hsum : euclideanSq (M.mulVec η) = ∑ i, (M.mulVec η i) ^ 2 := by
    unfold euclideanSq dot
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsum, Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ => coercInv_mulVec_row_sq_le M η i

theorem coercive_inv_of_coercive_of_frobenius {d : ℕ} {M : Mat d} {lam Λ : ℝ}
    (hlam : 0 < lam)
    (hcoer : ∀ ξ : Vec d, lam * euclideanSq ξ ≤ dot ξ (M.mulVec ξ))
    (hfrob : (∑ i, ∑ j, |M i j| ^ 2) ≤ Λ ^ 2) :
    IsUnit M.det ∧ ∀ ξ : Vec d, lam / Λ ^ 2 * euclideanSq ξ ≤ dot ξ (M⁻¹.mulVec ξ) := by
  -- A nonzero kernel vector `v` would give `lam |v|² ≤ v · M v = 0`.
  have hdet : IsUnit M.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨v, hv, hMv⟩ := (Matrix.exists_mulVec_eq_zero_iff (M := M)).mpr h0
    have hdot : dot v (M.mulVec v) = 0 := by
      rw [hMv]
      simp [dot]
    have hlp : 0 < lam * euclideanSq v := mul_pos hlam (coercInv_euclideanSq_pos hv)
    have hq := hcoer v
    linarith
  refine ⟨hdet, fun ξ => ?_⟩
  -- With `η = M⁻¹ ξ` we have `M η = ξ`.
  have hmul : M.mulVec (M⁻¹.mulVec ξ) = ξ := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv (A := M) hdet, Matrix.one_mulVec]
  -- Coercivity at `η`: `lam |η|² ≤ η · M η = η · ξ`.
  have hlow : lam * euclideanSq (M⁻¹.mulVec ξ) ≤ dot (M⁻¹.mulVec ξ) ξ := by
    have h := hcoer (M⁻¹.mulVec ξ)
    rw [hmul] at h
    exact h
  -- Frobenius bound at `η`: `|ξ|² = |M η|² ≤ Λ² |η|²`.
  have hup : euclideanSq ξ ≤ Λ ^ 2 * euclideanSq (M⁻¹.mulVec ξ) := by
    have h := coercInv_euclideanSq_mulVec_le M (M⁻¹.mulVec ξ)
    rw [hmul] at h
    exact h.trans (mul_le_mul_of_nonneg_right hfrob
      (coercInv_euclideanSq_nonneg (M⁻¹.mulVec ξ)))
  have hsym : dot ξ (M⁻¹.mulVec ξ) = dot (M⁻¹.mulVec ξ) ξ := coercInv_dot_comm _ _
  have hfrob_nonneg : 0 ≤ ∑ i, ∑ j, |M i j| ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hΛ2 : 0 ≤ Λ ^ 2 := le_trans hfrob_nonneg hfrob
  have hq0 : 0 ≤ lam * euclideanSq (M⁻¹.mulVec ξ) :=
    mul_nonneg hlam.le (coercInv_euclideanSq_nonneg (M⁻¹.mulVec ξ))
  rcases hΛ2.eq_or_lt with h0 | hpos
  · -- Degenerate bound `Λ² = 0`: the left side vanishes.
    rw [← h0, div_zero, zero_mul]
    linarith
  · have hcancel : lam / Λ ^ 2 * Λ ^ 2 = lam := div_mul_cancel₀ lam hpos.ne'
    calc lam / Λ ^ 2 * euclideanSq ξ
        ≤ lam / Λ ^ 2 * (Λ ^ 2 * euclideanSq (M⁻¹.mulVec ξ)) :=
          mul_le_mul_of_nonneg_left hup (div_nonneg hlam.le hΛ2)
      _ = lam * euclideanSq (M⁻¹.mulVec ξ) := by
          rw [← mul_assoc, hcancel]
      _ ≤ dot (M⁻¹.mulVec ξ) ξ := hlow
      _ = dot ξ (M⁻¹.mulVec ξ) := hsym.symm

end EinsteinRelation.Correctors
