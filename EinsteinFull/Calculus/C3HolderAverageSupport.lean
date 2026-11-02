import EinsteinFull.Calculus.ScalarWeightSupport

/-! Numerical scale selection and discrete iteration for `paper/main.tex:700–705`.
These lemmas consume a comparison estimate; they do not construct a caloric
comparison or prove an estimate for the actual endpoints. -/

namespace EinsteinFull

/-- Choose the interior fraction before the force threshold, using only the
unforced exponent and comparison constant. -/
theorem holder_comparison_scales (d : ℕ) (C α₀ : ℝ)
    (hC : 1 ≤ C) (hα : 0 < α₀) :
    ∃ θ c : ℝ, 0 < θ ∧ θ ≤ 1 / 2 ∧ 0 < c ∧
      ∀ m r : ℝ, m * r ≤ c →
        C * θ ^ α₀ + C * θ ^ (-((d : ℝ) + 2) / 2) * (m * r) ≤
          (θ / 2) ^ (α₀ / 2) := by
  let B := max 1 (C * (2 : ℝ) ^ (α₀ / 2))
  obtain ⟨hθ, hθhalf, habsorb⟩ :=
    inner_smoothing_absorption (1 / 2) B α₀ (by norm_num) (le_max_left _ _) hα
  let θ := min (1 / 2 : ℝ) ((2 * B) ^ (-2 / α₀))
  change 0 < θ at hθ
  change θ ≤ 1 / 2 at hθhalf
  change B * θ ^ (α₀ / 2) ≤ 1 / 2 at habsorb
  have hCp : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hpow : 0 < θ ^ (α₀ / 2) := Real.rpow_pos_of_pos hθ _
  have htwo : 0 < (2 : ℝ) ^ (α₀ / 2) := Real.rpow_pos_of_pos (by norm_num) _
  have hfirst : C * θ ^ α₀ ≤ (1 / 2 : ℝ) * (θ / 2) ^ (α₀ / 2) := by
    have hb := (mul_le_mul_of_nonneg_right (le_max_right 1
      (C * (2 : ℝ) ^ (α₀ / 2))) hpow.le).trans habsorb
    have hh := mul_le_mul_of_nonneg_right hb (div_nonneg hpow.le htwo.le)
    rw [Real.div_rpow hθ.le (by norm_num)]
    have he : θ ^ α₀ = θ ^ (α₀ / 2) * θ ^ (α₀ / 2) := by
      rw [← Real.rpow_add hθ]
      congr 1
      ring
    rw [he]
    change C * (2 : ℝ) ^ (α₀ / 2) * θ ^ (α₀ / 2) *
      (θ ^ (α₀ / 2) / (2 : ℝ) ^ (α₀ / 2)) ≤ _ at hh
    convert hh using 1
    field_simp
  let K := C * θ ^ (-((d : ℝ) + 2) / 2)
  have hK : 0 < K := mul_pos hCp (Real.rpow_pos_of_pos hθ _)
  let c := ((1 / 2 : ℝ) * (θ / 2) ^ (α₀ / 2)) / K
  have hc : 0 < c := div_pos
    (mul_pos (by norm_num) (Real.rpow_pos_of_pos (div_pos hθ (by norm_num)) _)) hK
  refine ⟨θ, c, hθ, hθhalf, hc, ?_⟩
  intro m r hmr
  have hsecond := mul_le_mul_of_nonneg_left hmr hK.le
  have hcancel : K * c = (1 / 2 : ℝ) * (θ / 2) ^ (α₀ / 2) := by
    dsimp only [c]
    field_simp
  rw [hcancel] at hsecond
  change C * θ ^ (-((d : ℝ) + 2) / 2) * (m * r) ≤ _ at hsecond
  linarith only [hfirst, hsecond]

/-- Iteration of a contraction on concentric geometric scales. -/
theorem holder_geometric_iteration (E : ℝ → ℝ) (q R α : ℝ) (hq : 0 ≤ q)
    (hstep : ∀ n : ℕ, E (q ^ (n + 1) * R) ≤ q ^ α * E (q ^ n * R)) :
    ∀ n : ℕ, E (q ^ n * R) ≤ (q ^ α) ^ n * E R := by
  intro n
  induction n with
  | zero => simp only [pow_zero, one_mul, le_refl]
  | succ n ih =>
    calc
      _ ≤ q ^ α * E (q ^ n * R) := hstep n
      _ ≤ q ^ α * ((q ^ α) ^ n * E R) :=
        mul_le_mul_of_nonneg_left ih (Real.rpow_nonneg hq _)
      _ = _ := by rw [pow_succ]; ring

/-- The two-radius comparison in the manuscript gives decay on every smaller
geometric scale while the original radius lies in the small-force regime. -/
theorem holder_comparison_iteration (d : ℕ) (C α₀ : ℝ)
    (hC : 1 ≤ C) (hα : 0 < α₀) :
    ∃ θ c : ℝ, 0 < θ ∧ θ ≤ 1 / 2 ∧ 0 < c ∧
      ∀ (E : ℝ → ℝ) (m R : ℝ), 0 ≤ m → 0 < R → m * R / 2 ≤ c →
        (∀ r : ℝ, 0 < r → E r ≥ 0) →
        (∀ r : ℝ, 0 < r → r ≤ R / 2 →
          E (θ * r) ≤
            (C * θ ^ α₀ + C * θ ^ (-((d : ℝ) + 2) / 2) * (m * r)) * E (2 * r)) →
        ∀ n : ℕ, E ((θ / 2) ^ n * R) ≤
          ((θ / 2) ^ (α₀ / 2)) ^ n * E R := by
  obtain ⟨θ, c, hθ, hθhalf, hc, hcontract⟩ := holder_comparison_scales d C α₀ hC hα
  refine ⟨θ, c, hθ, hθhalf, hc, ?_⟩
  intro E m R hm hR hsmall hE hcomparison
  apply holder_geometric_iteration E (θ / 2) R (α₀ / 2) (by positivity)
  intro n
  let r := (θ / 2) ^ n * R / 2
  have hr : 0 < r := by dsimp only [r]; positivity
  have hrR : r ≤ R / 2 := by
    have hp : (θ / 2) ^ n ≤ 1 := pow_le_one₀ (by positivity) (by linarith only [hθhalf])
    exact div_le_div_of_nonneg_right (mul_le_of_le_one_left hR.le hp) (by norm_num)
  have hmr : m * r ≤ c :=
    (mul_le_mul_of_nonneg_left hrR hm).trans (by nlinarith only [hsmall])
  have hb := (hcomparison r hr hrR).trans
    (mul_le_mul_of_nonneg_right (hcontract m r hmr) (hE (2 * r) (by positivity)))
  have houter : 2 * r = (θ / 2) ^ n * R := by dsimp only [r]; ring
  have hinner : θ * r = (θ / 2) ^ (n + 1) * R := by
    dsimp only [r]
    rw [pow_succ]
    ring
  rw [houter, hinner] at hb
  exact hb

end EinsteinFull
