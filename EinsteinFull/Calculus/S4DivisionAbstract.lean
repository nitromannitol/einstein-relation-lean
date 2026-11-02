import EinsteinFull.Calculus.S4DivisionElementary
import EinsteinFull.Calculus.S4ReciprocalVector
import Mathlib.Tactic.Module

/-!
# The abstract division lemma

The reciprocal expansion of `η = m + Σ_j e_j λ^{j+1} - 2 χ₀ T + R` and the corresponding
velocity expansion `η⁻¹ ℓ`, with constants depending only on `d`, the coefficient bound `C₁` and
the bound `Λ` on `|m⁻¹|`, `|η⁻¹|`.  The proof is split into small lemmas to keep each
declaration cheap.
-/

open Finset

namespace EinsteinFull

theorem expansionModulus_le_one {s : ℝ} (hs : 0 < s) (h : s ≤ Real.exp (-1)) :
    expansionModulus s hs h ≤ 1 :=
  Real.exp_le_one_iff.2 (neg_nonpos.2 (Real.sqrt_nonneg _))

theorem expansionModulus_pos {s : ℝ} (hs : 0 < s) (h : s ≤ Real.exp (-1)) :
    0 < expansionModulus s hs h := Real.exp_pos _

theorem pow_le_self_of_le_one {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) {n : ℕ} (hn : 1 ≤ n) :
    s ^ n ≤ s :=
  calc s ^ n ≤ s ^ 1 := pow_le_pow_of_le_one hs0.le hs1 hn
    _ = s := pow_one s

theorem T_bounds {d : ℕ} (hd : 2 ≤ d) {s M Lg T : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) (hM1 : M ≤ 1)
    (h4 : s * (1 + Lg) ≤ 4 * M) (hT : |T| ≤ s ^ d * (1 + Lg)) :
    |T| * s ≤ 4 * M * s ^ d ∧ |T| ≤ 4 * s := by
  have hsd : s ^ d = s ^ (d - 1) * s := by
    rw [← pow_succ]; congr 1; omega
  constructor
  · calc |T| * s ≤ s ^ d * (1 + Lg) * s := mul_le_mul_of_nonneg_right hT hs0.le
      _ = s ^ d * (s * (1 + Lg)) := by ring
      _ ≤ s ^ d * (4 * M) := mul_le_mul_of_nonneg_left h4 (pow_nonneg hs0.le _)
      _ = 4 * M * s ^ d := by ring
  · calc |T| ≤ s ^ d * (1 + Lg) := hT
      _ = s ^ (d - 1) * (s * (1 + Lg)) := by rw [hsd]; ring
      _ ≤ s ^ (d - 1) * (4 * M) := mul_le_mul_of_nonneg_left h4 (pow_nonneg hs0.le _)
      _ ≤ s ^ (d - 1) * 4 := mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hs0.le _)
      _ ≤ s * 4 := mul_le_mul_of_nonneg_right (pow_le_self_of_le_one hs0 hs1 (by omega))
          (by norm_num)
      _ = 4 * s := mul_comm _ _

theorem abs_poly_le {d : ℕ} {C₁ s : ℝ} (hC₁ : 0 ≤ C₁) (hs0 : 0 < s) (hs1 : s ≤ 1) {x : ℝ}
    (hx : |x| = s) (e : ℕ → ℝ) (he : ∀ j, |e j| ≤ C₁) :
    |∑ j ∈ range d, e j * x ^ (j + 1)| ≤ d * C₁ * s := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j ∈ range d, |e j * x ^ (j + 1)| ≤ ∑ j ∈ range d, C₁ * s := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul, abs_pow, hx]
        exact mul_le_mul (he j) (pow_le_self_of_le_one hs0 hs1 (by omega))
          (pow_nonneg hs0.le _) hC₁
    _ = d * C₁ * s := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

theorem abs_series_le {d : ℕ} {B s : ℝ} (hB0 : 0 ≤ B) (hs0 : 0 < s) (hs1 : s ≤ 1) {x : ℝ}
    (hx : |x| = s) (r : ℕ → ℝ) (hr : ∀ p, p ≤ d → |r p| ≤ B) :
    |∑ n ∈ range (d + 1), r n * x ^ n| ≤ ((d : ℝ) + 1) * B := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ n ∈ range (d + 1), |r n * x ^ n| ≤ ∑ n ∈ range (d + 1), B * 1 := by
        refine Finset.sum_le_sum fun n hn => ?_
        rw [abs_mul, abs_pow, hx]
        exact mul_le_mul (hr n (by have := mem_range.1 hn; omega)) (pow_le_one₀ hs0.le hs1)
          (pow_nonneg hs0.le _) hB0
    _ = ((d : ℝ) + 1) * B := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

theorem abs_series_sub_le {d : ℕ} {B s : ℝ} (hB0 : 0 ≤ B) (hs0 : 0 < s) (hs1 : s ≤ 1) {x : ℝ}
    (hx : |x| = s) (r : ℕ → ℝ) (hr : ∀ p, p ≤ d → |r p| ≤ B) :
    |∑ n ∈ range d, r (n + 1) * x ^ (n + 1)| ≤ d * B * s := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ n ∈ range d, |r (n + 1) * x ^ (n + 1)| ≤ ∑ n ∈ range d, B * s := by
        refine Finset.sum_le_sum fun n hn => ?_
        rw [abs_mul, abs_pow, hx]
        exact mul_le_mul (hr (n + 1) (by have := mem_range.1 hn; omega))
          (pow_le_self_of_le_one hs0 hs1 (by omega)) (pow_nonneg hs0.le _) hB0
    _ = d * B * s := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- `|η - m|` is `O(s)`. -/
theorem eta_sub_m_le {d : ℕ} {C₁ s P R T χ0 : ℝ} (hP : |P| ≤ d * C₁ * s) (hR : |R| ≤ C₁ * s)
    (hχ0 : |χ0| ≤ C₁) (hT : |T| ≤ 4 * s) (hC₁ : 0 ≤ C₁) :
    |P - 2 * χ0 * T + R| ≤ ((d : ℝ) + 9) * C₁ * s := by
  have h2 : |2 * χ0 * T| ≤ 2 * C₁ * (4 * s) := by
    rw [abs_mul, abs_mul, abs_two]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hχ0 (by norm_num)) hT (abs_nonneg _)
      (by positivity)
  have h3 := abs_sub P (2 * χ0 * T)
  have h4 := abs_add_le (P - 2 * χ0 * T) R
  linarith

/-- Final assembly of the scalar estimate, from the key identity and the pieces. -/
theorem scalar_final {m η S P R T χ0 Λ K₁ K₃ C₁ s M Sb : ℝ} {d : ℕ} (hm : m ≠ 0) (hη : η ≠ 0)
    (hΛ : 0 ≤ Λ) (hK₃0 : 0 ≤ K₃) (hC₁ : 0 ≤ C₁) (hs0 : 0 < s) (hM0 : 0 < M)
    (hηΛ : |η⁻¹| ≤ Λ) (hSb : |S| ≤ Sb)
    (hRdef : R = η - (m + P) + 2 * χ0 * T) (hRb : |R| ≤ C₁ * (s ^ d * M)) (hχ0 : |χ0| ≤ C₁)
    (hTs : |T| * s ≤ 4 * M * s ^ d) (hmix : |η⁻¹ * S - m⁻¹ * m⁻¹| ≤ K₃ * s)
    (hSQ : |S * (m + P) - 1| ≤ K₁ * (s ^ d * M)) :
    |η⁻¹ - S - (2 * χ0 / m ^ 2) * T| ≤ (Λ * K₁ + Λ * Sb * C₁ + 8 * C₁ * K₃) * (s ^ d * M) := by
  have key : η⁻¹ - S - (2 * χ0 / m ^ 2) * T =
      η⁻¹ * (1 - S * (m + P)) - η⁻¹ * S * R + 2 * χ0 * T * (η⁻¹ * S - m⁻¹ * m⁻¹) := by
    rw [hRdef]
    field_simp
    ring
  rw [key]
  have hpos : 0 ≤ s ^ d * M := by positivity
  have t1 : |η⁻¹ * (1 - S * (m + P))| ≤ Λ * K₁ * (s ^ d * M) := by
    rw [abs_mul, abs_sub_comm]
    calc |η⁻¹| * |S * (m + P) - 1| ≤ Λ * (K₁ * (s ^ d * M)) :=
          mul_le_mul hηΛ hSQ (abs_nonneg _) hΛ
      _ = Λ * K₁ * (s ^ d * M) := by ring
  have t2 : |η⁻¹ * S * R| ≤ Λ * Sb * (C₁ * (s ^ d * M)) := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul hηΛ hSb (abs_nonneg _) hΛ) hRb (abs_nonneg _)
      (mul_nonneg hΛ ((abs_nonneg _).trans hSb))
  have t3 : |2 * χ0 * T * (η⁻¹ * S - m⁻¹ * m⁻¹)| ≤ 8 * C₁ * K₃ * (s ^ d * M) := by
    have h2 : |2 * χ0 * T| ≤ 2 * C₁ * |T| := by
      have h2a : |2 * χ0 * T| = 2 * |χ0| * |T| := by rw [abs_mul, abs_mul, abs_two]
      rw [h2a]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hχ0 (by norm_num))
        (abs_nonneg T)
    have h3 : |2 * χ0 * T| * |η⁻¹ * S - m⁻¹ * m⁻¹| ≤ (2 * C₁ * |T|) * (K₃ * s) :=
      mul_le_mul h2 hmix (abs_nonneg _) (by positivity)
    have h4 : 2 * C₁ * K₃ * (|T| * s) ≤ 2 * C₁ * K₃ * (4 * M * s ^ d) :=
      mul_le_mul_of_nonneg_left hTs (by positivity)
    have h5 : (2 * C₁ * |T|) * (K₃ * s) = 2 * C₁ * K₃ * (|T| * s) := by ring
    have h6 : 2 * C₁ * K₃ * (4 * M * s ^ d) = 8 * C₁ * K₃ * (s ^ d * M) := by ring
    rw [abs_mul]
    exact le_trans h3 (le_trans (le_of_eq h5) (le_trans h4 (le_of_eq h6)))
  have h1 := abs_sub (η⁻¹ * (1 - S * (m + P))) (η⁻¹ * S * R)
  have h2 := abs_add_le (η⁻¹ * (1 - S * (m + P)) - η⁻¹ * S * R)
    (2 * χ0 * T * (η⁻¹ * S - m⁻¹ * m⁻¹))
  have e : (Λ * K₁ + Λ * Sb * C₁ + 8 * C₁ * K₃) * (s ^ d * M) =
      Λ * K₁ * (s ^ d * M) + Λ * Sb * (C₁ * (s ^ d * M)) + 8 * C₁ * K₃ * (s ^ d * M) := by ring
  rw [e]
  linarith

/-- Scalar part: the reciprocal expansion of `η`. -/
theorem division_scalar (d : ℕ) (hd : 2 ≤ d) (C₁ Λ : ℝ) (hC₁ : 0 ≤ C₁) (hΛ : 0 ≤ Λ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (m η lam T χ0 : ℝ) (e : ℕ → ℝ) (hs0 : 0 < |lam|)
      (hs1 : |lam| ≤ Real.exp (-1)),
      m ≠ 0 → η ≠ 0 → |m⁻¹| ≤ Λ → |η⁻¹| ≤ Λ → (∀ j, |e j| ≤ C₁) → |χ0| ≤ C₁ →
      |T| ≤ |lam| ^ d * (1 + Real.log (1 / |lam|)) →
      |η - m - ∑ j ∈ range d, e j * lam ^ (j + 1) + 2 * χ0 * T| ≤
        C₁ * |lam| ^ d * expansionModulus |lam| hs0 hs1 →
      |η⁻¹ - ∑ n ∈ range (d + 1), recipSeq m e n * lam ^ n - (2 * χ0 / m ^ 2) * T| ≤
        K * |lam| ^ d * expansionModulus |lam| hs0 hs1 := by
  set B : ℝ := recipBound Λ C₁ d with hBdef
  have hB0 : 0 ≤ B := recipBound_nonneg hΛ hC₁ d
  set K₂ : ℝ := ((d : ℝ) + 9) * C₁ with hK₂
  set K₃ : ℝ := Λ * d * B + Λ ^ 3 * K₂ with hK₃
  set K₁ : ℝ := (d : ℝ) * d * C₁ * B with hK₁
  have hK₂0 : 0 ≤ K₂ := by positivity
  have hK₃0 : 0 ≤ K₃ := by positivity
  have hK₁0 : 0 ≤ K₁ := by positivity
  refine ⟨Λ * K₁ + Λ * (((d : ℝ) + 1) * B) * C₁ + 8 * C₁ * K₃, by positivity, ?_⟩
  intro m η lam T χ0 e hs0 hs1 hm hη hmΛ hηΛ he hχ0 hT H1
  set s : ℝ := |lam| with hsdef
  set M : ℝ := expansionModulus s hs0 hs1 with hMdef
  have hM0 : 0 < M := expansionModulus_pos hs0 hs1
  have hM1 : M ≤ 1 := expansionModulus_le_one hs0 hs1
  have hsM : s ≤ M := le_expansionModulus hs0 hs1
  have h4 : s * (1 + Real.log (1 / s)) ≤ 4 * M := mul_one_add_log_le hs0 hs1
  have hs1' : s ≤ 1 := hs1.trans (by rw [Real.exp_le_one_iff]; norm_num)
  have hBp : ∀ p, p ≤ d → |recipSeq m e p| ≤ B := fun p hp =>
    abs_recipSeq_le hmΛ hΛ hC₁ he d p hp
  obtain ⟨hTs, hT4⟩ := T_bounds hd hs0 hs1' hM1 h4 hT
  have hPb := abs_poly_le (d := d) hC₁ hs0 hs1' (x := lam) rfl e he
  set P : ℝ := ∑ j ∈ range d, e j * lam ^ (j + 1) with hPdef
  set R : ℝ := η - (m + P) + 2 * χ0 * T with hRdef
  have hRb : |R| ≤ C₁ * s ^ d * M := by
    have : R = η - m - P + 2 * χ0 * T := by rw [hRdef]; ring
    rw [this]; exact H1
  have hsdM : s ^ d * M ≤ s := by
    have h1 : s ^ d ≤ s := pow_le_self_of_le_one hs0 hs1' (by omega)
    calc s ^ d * M ≤ s * 1 := mul_le_mul h1 hM1 hM0.le hs0.le
      _ = s := mul_one s
  have hRs : |R| ≤ C₁ * s := by
    calc |R| ≤ C₁ * s ^ d * M := hRb
      _ = C₁ * (s ^ d * M) := by ring
      _ ≤ C₁ * s := mul_le_mul_of_nonneg_left hsdM hC₁
  have hηm : |η - m| ≤ K₂ * s := by
    have e1 : η - m = P - 2 * χ0 * T + R := by rw [hRdef]; ring
    rw [e1, hK₂]
    exact eta_sub_m_le hPb hRs hχ0 hT4 hC₁
  have hηinv : |η⁻¹ - m⁻¹| ≤ Λ ^ 2 * K₂ * s := by
    have e1 : η⁻¹ - m⁻¹ = (m - η) * (η⁻¹ * m⁻¹) := by field_simp
    rw [e1, abs_mul, abs_mul, ← abs_neg (m - η), neg_sub]
    calc |η - m| * (|η⁻¹| * |m⁻¹|) ≤ (K₂ * s) * (Λ * Λ) :=
          mul_le_mul hηm (mul_le_mul hηΛ hmΛ (abs_nonneg _) hΛ) (by positivity) (by positivity)
      _ = Λ ^ 2 * K₂ * s := by ring
  set S : ℝ := ∑ n ∈ range (d + 1), recipSeq m e n * lam ^ n with hSdef
  have hSb : |S| ≤ ((d : ℝ) + 1) * B :=
    abs_series_le (d := d) hB0 hs0 hs1' (x := lam) rfl (recipSeq m e) hBp
  have hSm : |S - m⁻¹| ≤ d * B * s := by
    have e1 : S - m⁻¹ = ∑ n ∈ range d, recipSeq m e (n + 1) * lam ^ (n + 1) := by
      rw [hSdef, Finset.sum_range_succ' (fun n => recipSeq m e n * lam ^ n), recipSeq_zero]
      simp
    rw [e1]
    exact abs_series_sub_le (d := d) hB0 hs0 hs1' (x := lam) rfl (recipSeq m e) hBp
  have hSQ : |S * (m + P) - 1| ≤ K₁ * s ^ (d + 1) :=
    recip_tail hm e d he hBp hs1'
  have hSQ' : |S * (m + P) - 1| ≤ K₁ * (s ^ d * M) := by
    refine hSQ.trans (mul_le_mul_of_nonneg_left ?_ hK₁0)
    rw [pow_succ]
    exact mul_le_mul_of_nonneg_left hsM (pow_nonneg hs0.le _)
  have hmix : |η⁻¹ * S - m⁻¹ * m⁻¹| ≤ K₃ * s := by
    have e1 : η⁻¹ * S - m⁻¹ * m⁻¹ = η⁻¹ * (S - m⁻¹) + m⁻¹ * (η⁻¹ - m⁻¹) := by ring
    rw [e1]
    calc |η⁻¹ * (S - m⁻¹) + m⁻¹ * (η⁻¹ - m⁻¹)|
        ≤ |η⁻¹ * (S - m⁻¹)| + |m⁻¹ * (η⁻¹ - m⁻¹)| := abs_add_le _ _
      _ = |η⁻¹| * |S - m⁻¹| + |m⁻¹| * |η⁻¹ - m⁻¹| := by rw [abs_mul, abs_mul]
      _ ≤ Λ * (d * B * s) + Λ * (Λ ^ 2 * K₂ * s) :=
          add_le_add (mul_le_mul hηΛ hSm (abs_nonneg _) hΛ)
            (mul_le_mul hmΛ hηinv (abs_nonneg _) hΛ)
      _ = K₃ * s := by rw [hK₃]; ring
  have hRb' : |R| ≤ C₁ * (s ^ d * M) := by
    calc |R| ≤ C₁ * s ^ d * M := hRb
      _ = C₁ * (s ^ d * M) := by ring
  have := scalar_final (d := d) hm hη hΛ hK₃0 hC₁ hs0 hM0 hηΛ hSb hRdef hRb' hχ0 hTs hmix hSQ'
  calc _ ≤ (Λ * K₁ + Λ * (((d : ℝ) + 1) * B) * C₁ + 8 * C₁ * K₃) * (s ^ d * M) := this
    _ = (Λ * K₁ + Λ * (((d : ℝ) + 1) * B) * C₁ + 8 * C₁ * K₃) * s ^ d * M := by ring

end EinsteinFull
