import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Reciprocal power series with explicit truncation errors

`recipSeq m e` is the coefficient sequence of the reciprocal of `m + Σ_j e_j x^{j+1}`:
`r₀ = m⁻¹`, `r_{n+1} = -m⁻¹ Σ_{j ≤ n} e_j r_{n-j}`.  For `|x| ≤ 1` the truncation of the product is
controlled by `|x|^{d+1}`, and the corresponding vector Cauchy product with `a` by `|x|^{d+2}`.
-/

open Finset

namespace EinsteinFull

/-- Coefficients of the reciprocal of the power series `m + ∑ e j λ^(j+1)`. -/
noncomputable def recipSeq (m : ℝ) (e : ℕ → ℝ) : ℕ → ℝ
  | 0 => m⁻¹
  | n + 1 => -m⁻¹ * ∑ j : Fin (n + 1), e j * recipSeq m e (n - j)
decreasing_by all_goals simp_wf

theorem recipSeq_zero (m : ℝ) (e : ℕ → ℝ) : recipSeq m e 0 = m⁻¹ := by
  rw [recipSeq]

theorem recipSeq_succ (m : ℝ) (e : ℕ → ℝ) (n : ℕ) :
    recipSeq m e (n + 1) = -m⁻¹ * ∑ j ∈ range (n + 1), e j * recipSeq m e (n - j) := by
  rw [recipSeq]
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun j => e j * recipSeq m e (n - j)) (n + 1)

theorem m_mul_recipSeq_succ {m : ℝ} (hm : m ≠ 0) (e : ℕ → ℝ) (n : ℕ) :
    m * recipSeq m e (n + 1) = -∑ j ∈ range (n + 1), e j * recipSeq m e (n - j) := by
  rw [recipSeq_succ]
  field_simp

/-- Recursive bound for the reciprocal coefficients. -/
noncomputable def recipBound (Λ C : ℝ) : ℕ → ℝ
  | 0 => Λ
  | n + 1 => (1 + Λ * C * ((n : ℝ) + 1)) * recipBound Λ C n

theorem recipBound_nonneg {Λ C : ℝ} (hΛ : 0 ≤ Λ) (hC : 0 ≤ C) : ∀ n, 0 ≤ recipBound Λ C n
  | 0 => hΛ
  | n + 1 => by
      have := recipBound_nonneg hΛ hC n
      have h1 : 0 ≤ Λ * C * ((n : ℝ) + 1) := by positivity
      exact mul_nonneg (by linarith) this

theorem recipBound_mono {Λ C : ℝ} (hΛ : 0 ≤ Λ) (hC : 0 ≤ C) (n : ℕ) :
    recipBound Λ C n ≤ recipBound Λ C (n + 1) := by
  have := recipBound_nonneg hΛ hC n
  have h1 : 0 ≤ Λ * C * ((n : ℝ) + 1) := by positivity
  show recipBound Λ C n ≤ (1 + Λ * C * ((n : ℝ) + 1)) * recipBound Λ C n
  nlinarith

theorem abs_recipSeq_le {m : ℝ} {e : ℕ → ℝ} {Λ C : ℝ} (hΛ : |m⁻¹| ≤ Λ) (hΛ0 : 0 ≤ Λ)
    (hC0 : 0 ≤ C) (he : ∀ j, |e j| ≤ C) :
    ∀ n k, k ≤ n → |recipSeq m e k| ≤ recipBound Λ C n := by
  intro n
  induction n with
  | zero =>
    intro k hk
    have : k = 0 := by omega
    subst this
    rw [recipSeq_zero]
    exact hΛ
  | succ n ih =>
    intro k hk
    rcases Nat.lt_or_ge k (n + 1) with hlt | hge
    · exact (ih k (by omega)).trans (recipBound_mono hΛ0 hC0 n)
    · have hk' : k = n + 1 := by omega
      subst hk'
      rw [recipSeq_succ, abs_mul, abs_neg]
      have hsum : |∑ j ∈ range (n + 1), e j * recipSeq m e (n - j)| ≤
          (n + 1 : ℕ) * (C * recipBound Λ C n) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ j ∈ range (n + 1), |e j * recipSeq m e (n - j)|
            ≤ ∑ j ∈ range (n + 1), C * recipBound Λ C n := by
              refine Finset.sum_le_sum fun j hj => ?_
              rw [abs_mul]
              exact mul_le_mul (he j) (ih _ (by omega)) (abs_nonneg _) hC0
          _ = (n + 1 : ℕ) * (C * recipBound Λ C n) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hB0 := recipBound_nonneg hΛ0 hC0 n
      calc |m⁻¹| * |∑ j ∈ range (n + 1), e j * recipSeq m e (n - j)|
          ≤ Λ * ((n + 1 : ℕ) * (C * recipBound Λ C n)) :=
            mul_le_mul hΛ hsum (abs_nonneg _) hΛ0
        _ ≤ recipBound Λ C (n + 1) := by
            show _ ≤ (1 + Λ * C * ((n : ℝ) + 1)) * recipBound Λ C n
            push_cast
            nlinarith

theorem sum_range_sum_range_succ_swap {M : Type*} [AddCommMonoid M] (f : ℕ → ℕ → M) (N : ℕ) :
    ∑ n ∈ range N, ∑ k ∈ range (n + 1), f n k =
      ∑ k ∈ range N, ∑ p ∈ range (N - k), f (k + p) k := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih,
      Finset.sum_range_succ (fun k => ∑ p ∈ range (N + 1 - k), f (k + p) k)]
    have h1 : ∀ k ∈ range N, ∑ p ∈ range (N + 1 - k), f (k + p) k =
        ∑ p ∈ range (N - k), f (k + p) k + f N k := by
      intro k hk
      have hkN := mem_range.1 hk
      have h2 : N + 1 - k = (N - k) + 1 := by omega
      rw [h2, Finset.sum_range_succ]
      have h3 : k + (N - k) = N := by omega
      rw [h3]
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib,
      Finset.sum_range_succ (fun k => f N k)]
    have h2 : N + 1 - N = 1 := by omega
    rw [h2]
    simp only [Finset.sum_range_one, add_zero]
    abel

theorem recip_tail {m : ℝ} (hm : m ≠ 0) (e : ℕ → ℝ) (d : ℕ) {C B : ℝ}
    (he : ∀ j, |e j| ≤ C) (hB : ∀ p, p ≤ d → |recipSeq m e p| ≤ B) {x : ℝ} (hx : |x| ≤ 1) :
    |(∑ p ∈ range (d + 1), recipSeq m e p * x ^ p) * (m + ∑ j ∈ range d, e j * x ^ (j + 1)) - 1| ≤
      (d : ℝ) * d * C * B * |x| ^ (d + 1) := by
  set S := ∑ p ∈ range (d + 1), recipSeq m e p * x ^ p with hS
  have hmS : m * S = 1 - ∑ j ∈ range d, ∑ p ∈ range (d - j), e j * recipSeq m e p * x ^ (j + p + 1) := by
    have h0 : m * S = 1 + ∑ n ∈ range d, m * recipSeq m e (n + 1) * x ^ (n + 1) := by
      rw [hS, Finset.mul_sum, Finset.sum_range_succ' (fun p => m * (recipSeq m e p * x ^ p))]
      rw [recipSeq_zero]
      have : m * (m⁻¹ * x ^ 0) = 1 := by simp [hm]
      rw [this, add_comm]
      congr 1
      refine Finset.sum_congr rfl fun n _ => ?_
      ring
    rw [h0]
    have h1 : ∑ n ∈ range d, m * recipSeq m e (n + 1) * x ^ (n + 1) =
        -∑ n ∈ range d, ∑ j ∈ range (n + 1), e j * recipSeq m e (n - j) * x ^ (n + 1) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [m_mul_recipSeq_succ hm, neg_mul, Finset.sum_mul]
    rw [h1, sum_range_sum_range_succ_swap
      (fun n j => e j * recipSeq m e (n - j) * x ^ (n + 1)) d]
    simp only [Nat.add_sub_cancel_left]
    ring
  have hSA : (∑ j ∈ range d, e j * x ^ (j + 1)) * S =
      ∑ j ∈ range d, ∑ p ∈ range (d + 1), e j * recipSeq m e p * x ^ (j + p + 1) := by
    rw [hS, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun p _ => ?_
    ring
  have hprod : S * (m + ∑ j ∈ range d, e j * x ^ (j + 1)) - 1 =
      ∑ j ∈ range d, ∑ p ∈ Ico (d - j) (d + 1), e j * recipSeq m e p * x ^ (j + p + 1) := by
    have h1 : S * (m + ∑ j ∈ range d, e j * x ^ (j + 1)) =
        m * S + (∑ j ∈ range d, e j * x ^ (j + 1)) * S := by ring
    rw [h1, hmS, hSA]
    have h2 : ∀ j ∈ range d, ∑ p ∈ range (d + 1), e j * recipSeq m e p * x ^ (j + p + 1) =
        ∑ p ∈ range (d - j), e j * recipSeq m e p * x ^ (j + p + 1) +
          ∑ p ∈ Ico (d - j) (d + 1), e j * recipSeq m e p * x ^ (j + p + 1) := by
      intro j hj
      exact (Finset.sum_range_add_sum_Ico _ (by omega)).symm
    rw [Finset.sum_congr rfl h2, Finset.sum_add_distrib]
    ring
  rw [hprod]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j ∈ range d, |∑ p ∈ Ico (d - j) (d + 1), e j * recipSeq m e p * x ^ (j + p + 1)|
      ≤ ∑ j ∈ range d, (d : ℝ) * (C * B * |x| ^ (d + 1)) := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hjd := mem_range.1 hj
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ p ∈ Ico (d - j) (d + 1), |e j * recipSeq m e p * x ^ (j + p + 1)|
            ≤ ∑ p ∈ Ico (d - j) (d + 1), C * B * |x| ^ (d + 1) := by
              refine Finset.sum_le_sum fun p hp => ?_
              have hp' := mem_Ico.1 hp
              rw [abs_mul, abs_mul, abs_pow]
              have hC0 : 0 ≤ C := (abs_nonneg _).trans (he j)
              have hxp : |x| ^ (j + p + 1) ≤ |x| ^ (d + 1) :=
                pow_le_pow_of_le_one (abs_nonneg x) hx (by omega)
              exact mul_le_mul (mul_le_mul (he j) (hB p (by omega)) (abs_nonneg _) hC0) hxp
                (pow_nonneg (abs_nonneg _) _) (mul_nonneg hC0 ((abs_nonneg _).trans (hB p (by omega))))
          _ = ((Ico (d - j) (d + 1)).card : ℝ) * (C * B * |x| ^ (d + 1)) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (d : ℝ) * (C * B * |x| ^ (d + 1)) := by
              have hc : ((Ico (d - j) (d + 1)).card : ℝ) ≤ d := by
                rw [Nat.card_Ico]
                have : d + 1 - (d - j) ≤ d := by omega
                exact_mod_cast this
              have hC0 : 0 ≤ C := (abs_nonneg _).trans (he 0)
              have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 (Nat.zero_le _))
              exact mul_le_mul_of_nonneg_right hc (by positivity)
    _ = (d : ℝ) * d * C * B * |x| ^ (d + 1) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

end EinsteinFull
