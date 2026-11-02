import EinsteinFull.Calculus.S4DivisionConvert
import EinsteinFull.Calculus.S4DivisionClaims

/-!
# The quantitative conclusions of `e:division`, for one `(λ, ℓ, η)`

Given the expansions of `η` and `ℓ` from `e:numerator-clock` (in the statement's `Fin`-indexed,
`Vec d`-valued form) and the clock bounds, this proves the reciprocal and velocity expansions of
`e:division` with the explicit coefficients `divRecip`, `divB`, `divC`.
-/

open Finset EinsteinRelation EinsteinRelation.TimeChange

namespace EinsteinFull

theorem fin_sum_eta {d : ℕ} (etaC : Fin d → ℝ) (lam : ℝ) :
    ∑ j : Fin d, etaC j * lam ^ (j.val + 1) =
      ∑ j ∈ range d, etaExt d etaC j * lam ^ (j + 1) := by
  rw [← Fin.sum_univ_eq_sum_range (fun j => etaExt d etaC j * lam ^ (j + 1)) d]
  simp only [etaExt_apply]

theorem fin_sum_recip {d : ℕ} (m : ℝ) (etaC : Fin d → ℝ) (lam : ℝ) :
    ∑ n : Fin (d + 1), divRecip d m etaC n * lam ^ n.val =
      ∑ n ∈ range (d + 1), recipSeq m (etaExt d etaC) n * lam ^ n := by
  rw [← Fin.sum_univ_eq_sum_range (fun n => recipSeq m (etaExt d etaC) n * lam ^ n) (d + 1)]
  rfl

theorem norm_aE_le {d : ℕ} {C₁ : ℝ} (hC₁ : 0 ≤ C₁) {aVec : Fin (d + 1) → Vec d}
    (haC : ∀ n, euclideanNorm (aVec n) ≤ C₁) (k : ℕ) : ‖aE aVec k‖ ≤ C₁ := by
  unfold aE
  split_ifs with h
  · rw [← euclideanNorm_eq_norm_toEu]
    exact haC _
  · simpa using hC₁

theorem division_nine {d : ℕ} {C₁ Λ K₀ K₁ C : ℝ} (hC₁ : 0 < C₁) (hΛ : 1 ≤ Λ)
    (hK₀ : K₀ ≤ C) (hK₁ : K₁ ≤ C) (h16 : 16 ≤ C) (hΛC : Λ ≤ C)
    (hscal : ScalarClaim d C₁ Λ K₀) (hvec : VectorClaim (EuclideanSpace ℝ (Fin d)) d C₁ Λ K₁)
    {m : ℝ} {aVec : Fin (d + 1) → Vec d} {etaC : Fin d → ℝ} {χf : Option (Fin d) → ℝ}
    {Ae : Vec d} (hm : Λ⁻¹ ≤ m) (haC : ∀ n, euclideanNorm (aVec n) ≤ C₁)
    (hη : ∀ j, |etaC j| ≤ C₁)
    (hχ : euclideanNorm (fun i => χf (some i)) + |χf none| ≤ C₁)
    (hAe : aVec ⟨0, Nat.zero_lt_succ d⟩ = Ae)
    {lam : ℝ} {ell : Vec d} {η : ℝ} (h₀ : 0 < |lam|) (hsmall : |lam| ≤ Real.exp (-1))
    (hη1 : Λ⁻¹ ≤ η) (hη2 : η ≤ Λ)
    (H2 : euclideanNorm (ell - ∑ n : Fin (d + 1), lam ^ (n.val + 1) • aVec n +
        (2 * lam * criticalKernelTerm d lam (abs_pos.mp h₀)) • fun i => χf (some i)) ≤
      C₁ * |lam| ^ (d + 1) * expansionModulus |lam| h₀ hsmall)
    (H1 : |η - m - ∑ j : Fin d, etaC j * lam ^ (j.val + 1) +
        2 * χf none * criticalKernelTerm d lam (abs_pos.mp h₀)| ≤
      C₁ * |lam| ^ d * expansionModulus |lam| h₀ hsmall) :
    C⁻¹ ≤ m ∧ C⁻¹ ≤ η ∧ η ≤ C ∧
    |η⁻¹ - ∑ n : Fin (d + 1), divRecip d m etaC n * lam ^ n.val -
        2 * χf none / m ^ 2 * criticalKernelTerm d lam (abs_pos.mp h₀)| ≤
      C * |lam| ^ d * expansionModulus |lam| h₀ hsmall ∧
    euclideanNorm (η⁻¹ • ell - ∑ n : Fin (d + 1), lam ^ (n.val + 1) • divB d m etaC aVec n -
        criticalVelocityTerm d lam (abs_pos.mp h₀) • divC m χf Ae) ≤
      C * |lam| ^ (d + 1) * expansionModulus |lam| h₀ hsmall ∧
    |lam| ^ (d + 2) * (1 + Real.log (1 / |lam|)) ^ 2 ≤
      C * |lam| ^ (d + 1) * expansionModulus |lam| h₀ hsmall := by
  have hΛ0 : 0 < Λ := by linarith
  have hmpos : 0 < m := lt_of_lt_of_le (inv_pos.2 hΛ0) hm
  have hηpos : 0 < η := lt_of_lt_of_le (inv_pos.2 hΛ0) hη1
  have hmΛ : |m⁻¹| ≤ Λ := by
    rw [abs_of_pos (inv_pos.2 hmpos)]
    exact (inv_le_comm₀ hmpos hΛ0).2 hm
  have hηΛ : |η⁻¹| ≤ Λ := by
    rw [abs_of_pos (inv_pos.2 hηpos)]
    exact (inv_le_comm₀ hηpos hΛ0).2 hη1
  have hC0 : 0 < C := by linarith
  have hCΛ : C⁻¹ ≤ Λ⁻¹ := inv_anti₀ hΛ0 hΛC
  have hχ0 : |χf none| ≤ C₁ := by linarith [euclideanNorm_nonneg' (fun i => χf (some i))]
  have hχv : euclideanNorm (fun i => χf (some i)) ≤ C₁ := by linarith [abs_nonneg (χf none)]
  set T : ℝ := criticalKernelTerm d lam (abs_pos.mp h₀) with hTdef
  have hT : |T| ≤ |lam| ^ d * (1 + Real.log (1 / |lam|)) :=
    abs_criticalKernelTerm_le d (abs_pos.mp h₀) hsmall
  have hM0 : 0 < expansionModulus |lam| h₀ hsmall := expansionModulus_pos h₀ hsmall
  have hX0 : 0 ≤ |lam| ^ d * expansionModulus |lam| h₀ hsmall := by positivity
  have hX1 : 0 ≤ |lam| ^ (d + 1) * expansionModulus |lam| h₀ hsmall := by positivity
  have H1' : |η - m - ∑ j ∈ range d, etaExt d etaC j * lam ^ (j + 1) + 2 * χf none * T| ≤
      C₁ * |lam| ^ d * expansionModulus |lam| h₀ hsmall := by
    rw [← fin_sum_eta]; exact H1
  refine ⟨hCΛ.trans hm, hCΛ.trans hη1, hη2.trans hΛC, ?_, ?_, ?_⟩
  · have h := hscal m η lam T (χf none) (etaExt d etaC) h₀ hsmall hmpos.ne' hηpos.ne' hmΛ hηΛ
      (abs_etaExt_le hC₁.le hη) hχ0 hT H1'
    rw [fin_sum_recip]
    refine h.trans ?_
    linarith [mul_le_mul_of_nonneg_right hK₀ hX0]
  · have H2' : ‖toEu ell - ∑ k ∈ range (d + 1), lam ^ (k + 1) • aE aVec k +
        (2 * lam * T) • toEu (fun i => χf (some i))‖ ≤
        C₁ * |lam| ^ (d + 1) * expansionModulus |lam| h₀ hsmall := by
      rw [norm_conv_H2 lam T ell aVec (fun i => χf (some i))] at H2
      exact H2
    have h := hvec m η lam T (χf none) (etaExt d etaC) (aE aVec)
      (toEu fun i => χf (some i)) (toEu ell) h₀ hsmall hmpos.ne' hηpos.ne' hmΛ hηΛ
      (abs_etaExt_le hC₁.le hη) (norm_aE_le hC₁.le haC) hχ0
      (by rw [← euclideanNorm_eq_norm_toEu]; exact hχv) hT H1' H2'
    show euclideanNorm (η⁻¹ • ell - ∑ n : Fin (d + 1), lam ^ (n.val + 1) • divB d m etaC aVec n -
      (lam * T) • divC m χf Ae) ≤ _
    rw [norm_conv_G2 m η lam T χf etaC aVec ell Ae hAe]
    refine h.trans ?_
    linarith [mul_le_mul_of_nonneg_right hK₁ hX1]
  · have h := mul_one_add_log_sq_le h₀ hsmall
    calc |lam| ^ (d + 2) * (1 + Real.log (1 / |lam|)) ^ 2
        = |lam| ^ (d + 1) * (|lam| * (1 + Real.log (1 / |lam|)) ^ 2) := by ring
      _ ≤ |lam| ^ (d + 1) * (16 * expansionModulus |lam| h₀ hsmall) :=
          mul_le_mul_of_nonneg_left h (pow_nonneg (abs_nonneg _) _)
      _ ≤ |lam| ^ (d + 1) * (C * expansionModulus |lam| h₀ hsmall) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h16 hM0.le)
            (pow_nonneg (abs_nonneg _) _)
      _ = C * |lam| ^ (d + 1) * expansionModulus |lam| h₀ hsmall := by ring

end EinsteinFull
