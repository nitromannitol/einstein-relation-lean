import EinsteinFull.Calculus.S4DivisionAbstract

/-!
# The abstract division lemma, vector part

`η⁻¹ ℓ` against the Cauchy product `Σ_n λ^{n+1} b_n` and the critical term
`(λ T) • c`, with `c = (-2/m) χ_v + (2 χ₀/m²) a₀`.
-/

open Finset

namespace EinsteinFull

theorem norm_series_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {d : ℕ}
    {C₁ s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) {x : ℝ} (hx : |x| = s)
    (a : ℕ → E) (ha : ∀ k, ‖a k‖ ≤ C₁) :
    ‖∑ k ∈ range (d + 1), x ^ (k + 1) • a k‖ ≤ ((d : ℝ) + 1) * C₁ * s := by
  refine (norm_sum_le _ _).trans ?_
  calc ∑ k ∈ range (d + 1), ‖x ^ (k + 1) • a k‖ ≤ ∑ k ∈ range (d + 1), s * C₁ := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_smul, Real.norm_eq_abs, abs_pow, hx]
        exact mul_le_mul (pow_le_self_of_le_one hs0 hs1 (by omega)) (ha k) (norm_nonneg _) hs0.le
    _ = ((d : ℝ) + 1) * C₁ * s := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

theorem norm_series_sub_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {d : ℕ}
    {C₁ s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) {x : ℝ} (hx : |x| = s)
    (a : ℕ → E) (ha : ∀ k, ‖a k‖ ≤ C₁) :
    ‖(∑ k ∈ range (d + 1), x ^ (k + 1) • a k) - x • a 0‖ ≤ d * C₁ * s ^ 2 := by
  have e1 : (∑ k ∈ range (d + 1), x ^ (k + 1) • a k) - x • a 0 =
      ∑ k ∈ range d, x ^ (k + 1 + 1) • a (k + 1) := by
    rw [Finset.sum_range_succ' (fun k => x ^ (k + 1) • a k)]
    simp
  rw [e1]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ k ∈ range d, ‖x ^ (k + 1 + 1) • a (k + 1)‖ ≤ ∑ k ∈ range d, s ^ 2 * C₁ := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_smul, Real.norm_eq_abs, abs_pow, hx]
        exact mul_le_mul (pow_le_pow_of_le_one hs0.le hs1 (by omega)) (ha _) (norm_nonneg _)
          (pow_nonneg hs0.le _)
    _ = d * C₁ * s ^ 2 := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

theorem vec_identity {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u S c' T lam m : ℝ) (ell A a0 χv Bsum : E) :
    u • ell - Bsum - (lam * T) • ((-2 / m) • χv + c' • a0) =
      (S • A - Bsum) + ((c' * T) • (A - lam • a0)) + ((u - S - c' * T) • A) +
        ((-2 * (lam * T) * (u - m⁻¹)) • χv) + (u • (ell - A + (2 * (lam * T)) • χv)) := by
  module

/-- Vector part: the velocity expansion of `η⁻¹ ℓ`. -/
theorem division_vector {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d : ℕ) (hd : 2 ≤ d) (C₁ Λ : ℝ) (hC₁ : 0 ≤ C₁) (hΛ : 0 ≤ Λ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (m η lam T χ0 : ℝ) (e : ℕ → ℝ) (a : ℕ → E) (χv ell : E)
      (hs0 : 0 < |lam|) (hs1 : |lam| ≤ Real.exp (-1)),
      m ≠ 0 → η ≠ 0 → |m⁻¹| ≤ Λ → |η⁻¹| ≤ Λ → (∀ j, |e j| ≤ C₁) → (∀ k, ‖a k‖ ≤ C₁) →
      |χ0| ≤ C₁ → ‖χv‖ ≤ C₁ →
      |T| ≤ |lam| ^ d * (1 + Real.log (1 / |lam|)) →
      |η - m - ∑ j ∈ range d, e j * lam ^ (j + 1) + 2 * χ0 * T| ≤
        C₁ * |lam| ^ d * expansionModulus |lam| hs0 hs1 →
      ‖ell - ∑ k ∈ range (d + 1), lam ^ (k + 1) • a k + (2 * lam * T) • χv‖ ≤
        C₁ * |lam| ^ (d + 1) * expansionModulus |lam| hs0 hs1 →
      ‖η⁻¹ • ell - ∑ n ∈ range (d + 1), lam ^ (n + 1) •
          (∑ k ∈ range (n + 1), recipSeq m e (n - k) • a k) -
        (lam * T) • ((-2 / m) • χv + (2 * χ0 / m ^ 2) • a 0)‖ ≤
        K * |lam| ^ (d + 1) * expansionModulus |lam| hs0 hs1 := by
  obtain ⟨K₀, hK₀, hscal⟩ := division_scalar d hd C₁ Λ hC₁ hΛ
  set B : ℝ := recipBound Λ C₁ d with hBdef
  have hB0 : 0 ≤ B := recipBound_nonneg hΛ hC₁ d
  set K₂ : ℝ := ((d : ℝ) + 9) * C₁ with hK₂
  have hK₂0 : 0 ≤ K₂ := by positivity
  refine ⟨((d : ℝ) + 1) * ((d : ℝ) + 1) * B * C₁ + 8 * d * C₁ * C₁ * Λ ^ 2 +
    K₀ * ((d : ℝ) + 1) * C₁ + 8 * Λ ^ 2 * K₂ * C₁ + Λ * C₁, by positivity, ?_⟩
  intro m η lam T χ0 e a χv ell hs0 hs1 hm hη hmΛ hηΛ he ha hχ0 hχv hT H1 H2
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
  -- the scalar expansion and the closeness of η⁻¹ to m⁻¹
  have hE₂ := hscal m η lam T χ0 e hs0 hs1 hm hη hmΛ hηΛ he hχ0 hT H1
  have hPb := abs_poly_le (d := d) hC₁ hs0 hs1' (x := lam) rfl e he
  set P : ℝ := ∑ j ∈ range d, e j * lam ^ (j + 1) with hPdef
  set R : ℝ := η - (m + P) + 2 * χ0 * T with hRdef
  have hsdM : s ^ d * M ≤ s := by
    have h1 : s ^ d ≤ s := pow_le_self_of_le_one hs0 hs1' (by omega)
    calc s ^ d * M ≤ s * 1 := mul_le_mul h1 hM1 hM0.le hs0.le
      _ = s := mul_one s
  have hRs : |R| ≤ C₁ * s := by
    have h0 : R = η - m - P + 2 * χ0 * T := by rw [hRdef]; ring
    have hRb : |R| ≤ C₁ * s ^ d * M := by rw [h0]; exact H1
    calc |R| ≤ C₁ * s ^ d * M := hRb
      _ = C₁ * (s ^ d * M) := by ring
      _ ≤ C₁ * s := mul_le_mul_of_nonneg_left hsdM hC₁
  have hηm : |η - m| ≤ K₂ * s := by
    have e1 : η - m = P - 2 * χ0 * T + R := by rw [hRdef]; ring
    rw [e1, hK₂]
    exact eta_sub_m_le hPb hRs hχ0 hT4 hC₁
  have hηinv : |η⁻¹ - m⁻¹| ≤ Λ ^ 2 * K₂ * s := by
    have e1 : η⁻¹ - m⁻¹ = (η - m) * (-(η⁻¹ * m⁻¹)) := by field_simp; ring
    rw [e1, abs_mul, abs_neg, abs_mul]
    calc |η - m| * (|η⁻¹| * |m⁻¹|) ≤ (K₂ * s) * (Λ * Λ) :=
          mul_le_mul hηm (mul_le_mul hηΛ hmΛ (abs_nonneg _) hΛ) (by positivity) (by positivity)
      _ = Λ ^ 2 * K₂ * s := by ring
  -- the pieces
  set A : E := ∑ k ∈ range (d + 1), lam ^ (k + 1) • a k with hA
  set Bsum : E := ∑ n ∈ range (d + 1), lam ^ (n + 1) •
    (∑ k ∈ range (n + 1), recipSeq m e (n - k) • a k) with hBsum
  set S : ℝ := ∑ n ∈ range (d + 1), recipSeq m e n * lam ^ n with hSdef
  set c' : ℝ := 2 * χ0 / m ^ 2 with hc'def
  have hid := vec_identity (η⁻¹) S c' T lam m ell A (a 0) χv Bsum
  have hnorm : ‖η⁻¹ • ell - Bsum - (lam * T) • ((-2 / m) • χv + c' • a 0)‖ ≤
      ‖S • A - Bsum‖ + ‖(c' * T) • (A - lam • a 0)‖ + ‖(η⁻¹ - S - c' * T) • A‖ +
        ‖(-2 * (lam * T) * (η⁻¹ - m⁻¹)) • χv‖ + ‖η⁻¹ • (ell - A + (2 * (lam * T)) • χv)‖ := by
    rw [hid]
    refine (norm_add_le _ _).trans ?_
    refine add_le_add ((norm_add_le _ _).trans ?_) le_rfl
    refine add_le_add ((norm_add_le _ _).trans ?_) le_rfl
    exact add_le_add (norm_add_le _ _) le_rfl
  have hN0 : 0 ≤ s ^ (d + 1) * M := by positivity
  have hs2 : s ^ (d + 2) ≤ s ^ (d + 1) * M := by
    rw [pow_succ s (d + 1)]
    exact mul_le_mul_of_nonneg_left hsM (pow_nonneg hs0.le _)
  have hA : ‖A‖ ≤ ((d : ℝ) + 1) * C₁ * s :=
    norm_series_le (d := d) hs0 hs1' (x := lam) rfl a ha
  have hA0 : ‖A - lam • a 0‖ ≤ d * C₁ * s ^ 2 :=
    norm_series_sub_le (d := d) hs0 hs1' (x := lam) rfl a ha
  have hcb : |c'| ≤ 2 * C₁ * Λ ^ 2 := by
    have e1 : c' = 2 * χ0 * (m⁻¹ * m⁻¹) := by rw [hc'def]; field_simp
    rw [e1, abs_mul, abs_mul, abs_two]
    have h1 : |m⁻¹ * m⁻¹| ≤ Λ ^ 2 := by
      rw [abs_mul, sq]
      exact mul_le_mul hmΛ hmΛ (abs_nonneg _) hΛ
    exact mul_le_mul (mul_le_mul_of_nonneg_left hχ0 (by norm_num)) h1 (abs_nonneg _)
      (by positivity)
  -- t1
  have t1 : ‖S • A - Bsum‖ ≤ (((d : ℝ) + 1) * ((d : ℝ) + 1) * B * C₁) * (s ^ (d + 1) * M) := by
    have h := vec_tail m e d a (B := B) (Am := C₁) hBp ha (x := lam) hs1'
    refine h.trans ?_
    calc ((d : ℝ) + 1) * ((d : ℝ) + 1) * B * C₁ * s ^ (d + 2)
        ≤ ((d : ℝ) + 1) * ((d : ℝ) + 1) * B * C₁ * (s ^ (d + 1) * M) :=
          mul_le_mul_of_nonneg_left hs2 (by positivity)
      _ = _ := by ring
  -- t2
  have t2 : ‖(c' * T) • (A - lam • a 0)‖ ≤ (8 * d * C₁ * C₁ * Λ ^ 2) * (s ^ (d + 1) * M) := by
    rw [norm_smul, Real.norm_eq_abs, abs_mul]
    have h1 : |c'| * |T| ≤ (2 * C₁ * Λ ^ 2) * |T| := mul_le_mul_of_nonneg_right hcb (abs_nonneg _)
    have h2 : (|c'| * |T|) * ‖A - lam • a 0‖ ≤ ((2 * C₁ * Λ ^ 2) * |T|) * (d * C₁ * s ^ 2) :=
      mul_le_mul h1 hA0 (norm_nonneg _) (by positivity)
    have h3 : ((2 * C₁ * Λ ^ 2) * |T|) * (d * C₁ * s ^ 2) =
        (2 * C₁ * Λ ^ 2 * d * C₁ * s) * (|T| * s) := by ring
    have h4 : (2 * C₁ * Λ ^ 2 * d * C₁ * s) * (|T| * s) ≤
        (2 * C₁ * Λ ^ 2 * d * C₁ * s) * (4 * M * s ^ d) :=
      mul_le_mul_of_nonneg_left hTs (by positivity)
    have h5 : (2 * C₁ * Λ ^ 2 * d * C₁ * s) * (4 * M * s ^ d) =
        (8 * d * C₁ * C₁ * Λ ^ 2) * (s ^ (d + 1) * M) := by ring
    exact le_trans h2 (le_trans (le_of_eq h3) (le_trans h4 (le_of_eq h5)))
  -- t3
  have t3 : ‖(η⁻¹ - S - c' * T) • A‖ ≤ (K₀ * ((d : ℝ) + 1) * C₁) * (s ^ (d + 1) * M) := by
    rw [norm_smul, Real.norm_eq_abs]
    have h1 : |η⁻¹ - S - c' * T| * ‖A‖ ≤ (K₀ * s ^ d * M) * (((d : ℝ) + 1) * C₁ * s) :=
      mul_le_mul hE₂ hA (norm_nonneg _) (by positivity)
    have h2 : (K₀ * s ^ d * M) * (((d : ℝ) + 1) * C₁ * s) =
        (K₀ * ((d : ℝ) + 1) * C₁) * (s ^ (d + 1) * M) := by ring
    exact le_trans h1 (le_of_eq h2)
  -- t4
  have t4 : ‖(-2 * (lam * T) * (η⁻¹ - m⁻¹)) • χv‖ ≤
      (8 * Λ ^ 2 * K₂ * C₁) * (s ^ (d + 1) * M) := by
    rw [norm_smul, Real.norm_eq_abs]
    have h0 : |-2 * (lam * T) * (η⁻¹ - m⁻¹)| = 2 * s * |T| * |η⁻¹ - m⁻¹| := by
      rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_two, ← hsdef]
      ring
    have h1 : 2 * s * |T| * |η⁻¹ - m⁻¹| ≤ 2 * s * |T| * (Λ ^ 2 * K₂ * s) :=
      mul_le_mul_of_nonneg_left hηinv (by positivity)
    have h2 : 2 * s * |T| * (Λ ^ 2 * K₂ * s) = (2 * s * Λ ^ 2 * K₂) * (|T| * s) := by ring
    have h3 : (2 * s * Λ ^ 2 * K₂) * (|T| * s) ≤ (2 * s * Λ ^ 2 * K₂) * (4 * M * s ^ d) :=
      mul_le_mul_of_nonneg_left hTs (by positivity)
    have h4 : |-2 * (lam * T) * (η⁻¹ - m⁻¹)| ≤ (8 * Λ ^ 2 * K₂) * (s ^ (d + 1) * M) := by
      rw [h0]
      refine le_trans h1 (le_trans (le_of_eq h2) (le_trans h3 (le_of_eq ?_)))
      ring
    calc |-2 * (lam * T) * (η⁻¹ - m⁻¹)| * ‖χv‖
        ≤ ((8 * Λ ^ 2 * K₂) * (s ^ (d + 1) * M)) * C₁ :=
          mul_le_mul h4 hχv (norm_nonneg _) (by positivity)
      _ = (8 * Λ ^ 2 * K₂ * C₁) * (s ^ (d + 1) * M) := by ring
  -- t5
  have t5 : ‖η⁻¹ • (ell - A + (2 * (lam * T)) • χv)‖ ≤ (Λ * C₁) * (s ^ (d + 1) * M) := by
    rw [norm_smul, Real.norm_eq_abs]
    have hE1 : ‖ell - A + (2 * (lam * T)) • χv‖ ≤ C₁ * s ^ (d + 1) * M := by
      have e1 : (2 * (lam * T)) = 2 * lam * T := by ring
      rw [e1]; exact H2
    calc |η⁻¹| * ‖ell - A + (2 * (lam * T)) • χv‖ ≤ Λ * (C₁ * s ^ (d + 1) * M) :=
          mul_le_mul hηΛ hE1 (norm_nonneg _) hΛ
      _ = (Λ * C₁) * (s ^ (d + 1) * M) := by ring
  have hfin : ‖η⁻¹ • ell - Bsum - (lam * T) • ((-2 / m) • χv + c' • a 0)‖ ≤
      (((d : ℝ) + 1) * ((d : ℝ) + 1) * B * C₁ + 8 * d * C₁ * C₁ * Λ ^ 2 +
        K₀ * ((d : ℝ) + 1) * C₁ + 8 * Λ ^ 2 * K₂ * C₁ + Λ * C₁) * (s ^ (d + 1) * M) := by
    have e : (((d : ℝ) + 1) * ((d : ℝ) + 1) * B * C₁ + 8 * d * C₁ * C₁ * Λ ^ 2 +
        K₀ * ((d : ℝ) + 1) * C₁ + 8 * Λ ^ 2 * K₂ * C₁ + Λ * C₁) * (s ^ (d + 1) * M) =
        (((d : ℝ) + 1) * ((d : ℝ) + 1) * B * C₁) * (s ^ (d + 1) * M) +
        (8 * d * C₁ * C₁ * Λ ^ 2) * (s ^ (d + 1) * M) +
        (K₀ * ((d : ℝ) + 1) * C₁) * (s ^ (d + 1) * M) +
        (8 * Λ ^ 2 * K₂ * C₁) * (s ^ (d + 1) * M) + (Λ * C₁) * (s ^ (d + 1) * M) := by ring
    rw [e]
    linarith
  exact hfin.trans (le_of_eq (by rw [hsdef]; ring))

end EinsteinFull
