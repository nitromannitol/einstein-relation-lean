import EinsteinRelation.Environment.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace EinsteinRelation.Correctors

private theorem dot_mulVec_comm_of_symm {d : ℕ} (A : Mat d) (hA : A.transpose = A)
    (x y : Vec d) : dot x (A.mulVec y) = dot (A.mulVec x) y := by
  change dotProduct x (A.mulVec y) = dotProduct (A.mulVec x) y
  rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, hA]

/-- A positive symmetric quadratic bound gives the actual Euclidean operator bound,
with no dimension factor. Source main.tex198–207,688–701; an internal matrix estimate. -/
theorem mulVec_euclideanNorm_le_of_quadratic {d : ℕ} {L : ℝ} (A : Mat d)
    (hL : 0 < L) (hA : A.transpose = A)
    (hlow : ∀ ξ, 0 ≤ dot ξ (A.mulVec ξ))
    (hup : ∀ ξ, dot ξ (A.mulVec ξ) ≤ L * euclideanSq ξ) (ξ : Vec d) :
    euclideanNorm (A.mulVec ξ) ≤ L * euclideanNorm ξ := by
  have hc := dot_mulVec_comm_of_symm A hA ξ (A.mulVec ξ)
  have heq : dot (A.mulVec ξ - L • ξ) (A.mulVec (A.mulVec ξ - L • ξ)) =
      dot (A.mulVec ξ) (A.mulVec (A.mulVec ξ)) - 2*L*euclideanSq (A.mulVec ξ) +
        L^2 * dot ξ (A.mulVec ξ) := by
    change dotProduct (A.mulVec ξ - L • ξ) (A.mulVec (A.mulVec ξ - L • ξ)) = _
    simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct, dotProduct_sub,
      smul_dotProduct, dotProduct_smul, smul_eq_mul]
    change dot (A.mulVec ξ) (A.mulVec (A.mulVec ξ)) -
        L * dot ξ (A.mulVec (A.mulVec ξ)) -
        L * (dot (A.mulVec ξ) (A.mulVec ξ) - L * dot ξ (A.mulVec ξ)) = _
    rw [hc]
    unfold euclideanSq
    ring
  have hpos := hlow (A.mulVec ξ - L • ξ)
  rw [heq] at hpos
  have h1 := hup (A.mulVec ξ)
  have h2 := hup ξ
  have hscaled : 0 ≤ L^2 * (L * euclideanSq ξ - dot ξ (A.mulVec ξ)) :=
    mul_nonneg (sq_nonneg L) (sub_nonneg.mpr h2)
  have hdiff : 0 ≤ L * (L^2*euclideanSq ξ - euclideanSq (A.mulVec ξ)) := by
    nlinarith only [hpos, h1, hscaled]
  have hs : euclideanSq (A.mulVec ξ) ≤ L^2*euclideanSq ξ :=
    sub_nonneg.mp (nonneg_of_mul_nonneg_right hdiff hL)
  unfold euclideanNorm
  calc Real.sqrt (euclideanSq (A.mulVec ξ)) ≤ Real.sqrt (L^2*euclideanSq ξ) :=
      Real.sqrt_le_sqrt hs
    _ = L * Real.sqrt (euclideanSq ξ) := by rw [Real.sqrt_mul (sq_nonneg L), Real.sqrt_sq hL.le]

/-- The field ellipticity predicate controls multiplication in the exact Euclidean norm. -/
theorem isElliptic_mulVec_euclideanNorm_le {d : ℕ} {L : ℝ} {a : Vec d → Mat d}
    (hL : 0 < L) (ha : IsElliptic L a) (x ξ : Vec d) :
    euclideanNorm ((a x).mulVec ξ) ≤ L * euclideanNorm ξ := by
  apply mulVec_euclideanNorm_le_of_quadratic (a x) hL (ha x).1
  · intro η
    have hn : 0 ≤ euclideanSq η := by
      unfold euclideanSq dot
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg (η i)
    exact (mul_nonneg (inv_nonneg.mpr hL.le) hn).trans ((ha x).2 η).1
  · exact fun η => ((ha x).2 η).2
end EinsteinRelation.Correctors
