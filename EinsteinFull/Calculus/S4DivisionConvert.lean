import EinsteinFull.Calculus.S4DivisionPure

/-!
# Transport to `EuclideanSpace` for the division assembly

The abstract vector division lemma lives in a normed space with `ℕ`-indexed sums.  This file
transports the statement's `Vec d`-valued, `Fin`-indexed expressions to
`EuclideanSpace ℝ (Fin d)` through the linear equivalence `WithLp.linearEquiv`.
-/

open Finset EinsteinRelation EinsteinRelation.TimeChange

namespace EinsteinFull

/-- Coordinates as a Euclidean vector. -/
noncomputable def toEu {d : ℕ} : Vec d →ₗ[ℝ] EuclideanSpace ℝ (Fin d) :=
  (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).symm.toLinearMap

theorem toEu_apply {d : ℕ} (v : Vec d) : toEu v = WithLp.toLp 2 v := rfl

theorem euclideanNorm_eq_norm_toEu {d : ℕ} (v : Vec d) : euclideanNorm v = ‖toEu v‖ :=
  euclideanNorm_eq_norm_toLp v

/-- The expansion coefficients as a Euclidean sequence, zero past the last index. -/
noncomputable def aE {d : ℕ} (aVec : Fin (d + 1) → Vec d) : ℕ → EuclideanSpace ℝ (Fin d) :=
  fun k => if h : k < d + 1 then toEu (aVec ⟨k, h⟩) else 0

theorem aE_apply {d : ℕ} (aVec : Fin (d + 1) → Vec d) (n : Fin (d + 1)) :
    aE aVec n.val = toEu (aVec n) := by
  unfold aE
  rw [dif_pos n.isLt]

theorem norm_conv_H2 {d : ℕ} (lam T : ℝ) (ell : Vec d) (aVec : Fin (d + 1) → Vec d)
    (χvec : Vec d) :
    euclideanNorm (ell - ∑ n : Fin (d + 1), lam ^ (n.val + 1) • aVec n +
        (2 * lam * T) • χvec) =
      ‖toEu ell - ∑ k ∈ range (d + 1), lam ^ (k + 1) • aE aVec k +
        (2 * lam * T) • toEu χvec‖ := by
  rw [euclideanNorm_eq_norm_toEu]
  simp only [map_add, map_sub, map_smul, map_sum]
  rw [← Fin.sum_univ_eq_sum_range (fun k => lam ^ (k + 1) • aE aVec k) (d + 1)]
  simp only [aE_apply]

theorem norm_conv_G2 {d : ℕ} (m η lam T : ℝ) (χf : Option (Fin d) → ℝ) (etaC : Fin d → ℝ)
    (aVec : Fin (d + 1) → Vec d) (ell Ae : Vec d)
    (hAe : aVec ⟨0, Nat.zero_lt_succ d⟩ = Ae) :
    euclideanNorm (η⁻¹ • ell - ∑ n : Fin (d + 1), lam ^ (n.val + 1) • divB d m etaC aVec n -
        (lam * T) • divC m χf Ae) =
      ‖η⁻¹ • toEu ell - ∑ n ∈ range (d + 1), lam ^ (n + 1) •
          (∑ k ∈ range (n + 1), recipSeq m (etaExt d etaC) (n - k) • aE aVec k) -
        (lam * T) • ((-2 / m) • toEu (fun i => χf (some i)) +
          (2 * χf none / m ^ 2) • aE aVec 0)‖ := by
  rw [euclideanNorm_eq_norm_toEu]
  have hb : ∀ n : Fin (d + 1), toEu (divB d m etaC aVec n) =
      ∑ k ∈ range (n.val + 1), recipSeq m (etaExt d etaC) (n.val - k) • aE aVec k := by
    intro n
    unfold divB
    simp only [map_sum, map_smul]
    rw [← Fin.sum_univ_eq_sum_range (fun k => recipSeq m (etaExt d etaC) (n.val - k) • aE aVec k)
      (n.val + 1)]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h1 : aE aVec k.val = toEu (aVec ⟨k.val, Nat.lt_of_lt_of_le k.isLt
        (Nat.succ_le_of_lt n.isLt)⟩) := by
      unfold aE
      rw [dif_pos (Nat.lt_of_lt_of_le k.isLt (Nat.succ_le_of_lt n.isLt))]
    rw [h1]
    rfl
  have hc : toEu (divC m χf Ae) = (-2 / m) • toEu (fun i => χf (some i)) +
      (2 * χf none / m ^ 2) • aE aVec 0 := by
    rw [divC_eq, map_add, map_smul, map_smul]
    congr 2
    have : aE aVec 0 = toEu (aVec ⟨0, Nat.zero_lt_succ d⟩) := by
      unfold aE
      rw [dif_pos (Nat.zero_lt_succ d)]
    rw [this, hAe]
  simp only [map_sub, map_smul, map_sum, hb, hc]
  rw [← Fin.sum_univ_eq_sum_range (fun n => lam ^ (n + 1) •
    (∑ k ∈ range (n + 1), recipSeq m (etaExt d etaC) (n - k) • aE aVec k)) (d + 1)]

end EinsteinFull
