import EinsteinFull.Calculus.S4ReciprocalSeries
import Mathlib.Algebra.Module.BigOperators

/-!
# The vector Cauchy product with a reciprocal series

For `a : ℕ → E` and `b_n = Σ_{k ≤ n} r_{n-k} a_k`, the truncated product
`Σ_{n ≤ d} x^{n+1} b_n` differs from `(Σ_{p ≤ d} r_p x^p) • (Σ_{k ≤ d} x^{k+1} a_k)` by at most
`(d+1)² B A |x|^{d+2}` when `|x| ≤ 1`.
-/

open Finset

namespace EinsteinFull

theorem vec_tail {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (m : ℝ) (e : ℕ → ℝ)
    (d : ℕ) (a : ℕ → E) {B Am : ℝ} (hB : ∀ p, p ≤ d → |recipSeq m e p| ≤ B)
    (ha : ∀ k, ‖a k‖ ≤ Am) {x : ℝ} (hx : |x| ≤ 1) :
    ‖(∑ p ∈ range (d + 1), recipSeq m e p * x ^ p) • (∑ k ∈ range (d + 1), x ^ (k + 1) • a k) -
        ∑ n ∈ range (d + 1), x ^ (n + 1) • (∑ k ∈ range (n + 1), recipSeq m e (n - k) • a k)‖ ≤
      ((d : ℝ) + 1) * ((d : ℝ) + 1) * B * Am * |x| ^ (d + 2) := by
  have hfirst : (∑ p ∈ range (d + 1), recipSeq m e p * x ^ p) •
      (∑ k ∈ range (d + 1), x ^ (k + 1) • a k) =
      ∑ k ∈ range (d + 1), ∑ p ∈ range (d + 1), (recipSeq m e p * x ^ p * x ^ (k + 1)) • a k := by
    rw [Finset.sum_smul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun p _ => ?_
    rw [smul_smul]
  have hsecond : ∑ n ∈ range (d + 1), x ^ (n + 1) •
      (∑ k ∈ range (n + 1), recipSeq m e (n - k) • a k) =
      ∑ k ∈ range (d + 1), ∑ p ∈ range (d + 1 - k),
        (recipSeq m e p * x ^ p * x ^ (k + 1)) • a k := by
    have h1 : ∀ n ∈ range (d + 1), x ^ (n + 1) • (∑ k ∈ range (n + 1), recipSeq m e (n - k) • a k) =
        ∑ k ∈ range (n + 1), (x ^ (n + 1) * recipSeq m e (n - k)) • a k := by
      intro n _
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_smul]
    rw [Finset.sum_congr rfl h1,
      sum_range_sum_range_succ_swap (fun n k => (x ^ (n + 1) * recipSeq m e (n - k)) • a k) (d + 1)]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun p _ => ?_
    simp only [Nat.add_sub_cancel_left]
    congr 1
    ring
  have hdiff : (∑ k ∈ range (d + 1), ∑ p ∈ range (d + 1), (recipSeq m e p * x ^ p * x ^ (k + 1)) • a k) -
      ∑ k ∈ range (d + 1), ∑ p ∈ range (d + 1 - k),
        (recipSeq m e p * x ^ p * x ^ (k + 1)) • a k =
      ∑ k ∈ range (d + 1), ∑ p ∈ Ico (d + 1 - k) (d + 1),
        (recipSeq m e p * x ^ p * x ^ (k + 1)) • a k := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkd := mem_range.1 hk
    rw [← Finset.sum_range_add_sum_Ico _ (by omega : d + 1 - k ≤ d + 1)]
    abel
  rw [hfirst, hsecond, hdiff]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ k ∈ range (d + 1), ‖∑ p ∈ Ico (d + 1 - k) (d + 1),
        (recipSeq m e p * x ^ p * x ^ (k + 1)) • a k‖
      ≤ ∑ k ∈ range (d + 1), ((d : ℝ) + 1) * (B * Am * |x| ^ (d + 2)) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hkd := mem_range.1 hk
        refine (norm_sum_le _ _).trans ?_
        calc ∑ p ∈ Ico (d + 1 - k) (d + 1), ‖(recipSeq m e p * x ^ p * x ^ (k + 1)) • a k‖
            ≤ ∑ p ∈ Ico (d + 1 - k) (d + 1), B * Am * |x| ^ (d + 2) := by
              refine Finset.sum_le_sum fun p hp => ?_
              have hp' := mem_Ico.1 hp
              rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_pow]
              have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 (Nat.zero_le _))
              have hxp : |x| ^ p * |x| ^ (k + 1) ≤ |x| ^ (d + 2) := by
                rw [← pow_add]
                exact pow_le_pow_of_le_one (abs_nonneg x) hx (by omega)
              have hA0 : 0 ≤ Am := (norm_nonneg _).trans (ha 0)
              calc |recipSeq m e p| * |x| ^ p * |x| ^ (k + 1) * ‖a k‖
                  = (|recipSeq m e p| * (|x| ^ p * |x| ^ (k + 1))) * ‖a k‖ := by ring
                _ ≤ (B * |x| ^ (d + 2)) * Am := by
                    refine mul_le_mul (mul_le_mul (hB p (by omega)) hxp
                      (mul_nonneg (pow_nonneg (abs_nonneg _) _) (pow_nonneg (abs_nonneg _) _))
                      hB0) (ha k) (norm_nonneg _) (mul_nonneg hB0 (pow_nonneg (abs_nonneg _) _))
                _ = B * Am * |x| ^ (d + 2) := by ring
          _ = ((Ico (d + 1 - k) (d + 1)).card : ℝ) * (B * Am * |x| ^ (d + 2)) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ ((d : ℝ) + 1) * (B * Am * |x| ^ (d + 2)) := by
              have hc : ((Ico (d + 1 - k) (d + 1)).card : ℝ) ≤ (d : ℝ) + 1 := by
                rw [Nat.card_Ico]
                have : d + 1 - (d + 1 - k) ≤ d + 1 := by omega
                exact_mod_cast this
              have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 (Nat.zero_le _))
              have hA0 : 0 ≤ Am := (norm_nonneg _).trans (ha 0)
              exact mul_le_mul_of_nonneg_right hc (by positivity)
    _ = ((d : ℝ) + 1) * ((d : ℝ) + 1) * B * Am * |x| ^ (d + 2) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

end EinsteinFull
