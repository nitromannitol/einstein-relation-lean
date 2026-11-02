import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

open Filter
open scoped BigOperators Topology

noncomputable section
namespace EinsteinFull.Calculus

/-- Iterate an additive recurrence with a uniformly bounded terminal term. -/
theorem c17_bounded_additive_geometric_iteration
    (a b c T : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hac : a * c < 1) (X : ℕ → ℝ)
    (hX : ∀ n, X n ≤ T)
    (hstep : ∀ n, X n ≤ a * X (n + 1) + b * c ^ n) :
    X 0 ≤ b * ∑' n : ℕ, (a * c) ^ n := by
  have hq : 0 ≤ a * c := mul_nonneg ha hc
  have hs : Summable (fun n : ℕ => (a * c) ^ n) :=
    summable_geometric_of_lt_one hq hac
  have hi : ∀ N : ℕ, X 0 ≤ a ^ N * X N +
      b * ∑ n ∈ Finset.range N, (a * c) ^ n := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, mul_add, pow_succ]
      have h := mul_le_mul_of_nonneg_left (hstep N) (pow_nonneg ha N)
      rw [mul_add] at h
      rw [mul_pow]
      nlinarith
  have hall : ∀ N : ℕ, X 0 ≤ a ^ N * T + b * ∑' n : ℕ, (a * c) ^ n := by
    intro N
    have hsum := hs.sum_le_tsum (Finset.range N) (fun n _ => pow_nonneg hq n)
    have ht := mul_le_mul_of_nonneg_left (hX N) (pow_nonneg ha N)
    have hb' := mul_le_mul_of_nonneg_left hsum hb
    linarith [hi N]
  have hlim : Tendsto (fun N : ℕ => a ^ N * T + b * ∑' n : ℕ, (a * c) ^ n)
      atTop (𝓝 (b * ∑' n : ℕ, (a * c) ^ n)) := by
    simpa only [zero_mul, zero_add] using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one ha ha1).mul_const T).add_const
        (b * ∑' n : ℕ, (a * c) ^ n)
  exact ge_of_tendsto hlim (Filter.Eventually.of_forall hall)

/-- Scaled weighted AM-GM supplies an arbitrary positive absorption factor. -/
theorem c17_scaled_interpolation_young (θ a A x : ℝ)
    (hθ : 0 < θ) (hθ1 : θ < 1) (ha : 0 < a)
    (hA : 0 ≤ A) (hx : 0 ≤ x) :
    A * Real.rpow x (1 - θ) ≤ a * x +
      θ * Real.rpow (A / Real.rpow (a / (1 - θ)) (1 - θ)) (1 / θ) := by
  let d : ℝ := a / (1 - θ)
  have hd : 0 < d := div_pos ha (by linarith)
  have hd' : 0 < Real.rpow d (1 - θ) := Real.rpow_pos_of_pos hd _
  have hq : 0 ≤ A / Real.rpow d (1 - θ) := div_nonneg hA hd'.le
  simp only [Real.rpow_eq_pow] at hd' hq
  have h := Real.geom_mean_le_arith_mean2_weighted
    (w₁ := 1 - θ) (w₂ := θ) (p₁ := d * x)
    (p₂ := Real.rpow (A / Real.rpow d (1 - θ)) (1 / θ))
    (by linarith) hθ.le (mul_nonneg hd.le hx) (Real.rpow_nonneg hq _)
    (by ring)
  have heq : Real.rpow (d * x) (1 - θ) *
      Real.rpow (Real.rpow (A / Real.rpow d (1 - θ)) (1 / θ)) θ =
      A * Real.rpow x (1 - θ) := by
    simp only [Real.rpow_eq_pow]
    rw [Real.mul_rpow hd.le hx, ← Real.rpow_mul hq]
    have he : 1 / θ * θ = 1 := by field_simp
    rw [he, Real.rpow_one]
    field_simp
  simp only [Real.rpow_eq_pow] at heq h
  rw [heq] at h
  have heq' : (1 - θ) * (d * x) = a * x := by
    dsimp [d]
    field_simp [ne_of_gt (show 0 < 1 - θ by linarith)]
  rw [heq'] at h
  exact h

/-- Dyadic radii start at one half, remain in the unit interval, and have positive gaps. -/
theorem c17_dyadic_radii (n : ℕ) :
    (1 / 2 : ℝ) ≤ 1 - (1 / 2 : ℝ) ^ (n + 1) ∧
      1 - (1 / 2 : ℝ) ^ (n + 1) ≤ 1 ∧
      (1 - (1 / 2 : ℝ) ^ (n + 2)) - (1 - (1 / 2 : ℝ) ^ (n + 1)) =
        (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ n ∧
      0 < (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ n := by
  have hp : 0 < (1 / 2 : ℝ) ^ n := by positivity
  have hb : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  simp only [pow_succ]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · ring
  · positivity

/-- A small positive absorption factor makes any nonnegative geometric ratio summable. -/
theorem c17_absorption_factor (c : ℝ) (hc : 0 ≤ c) :
    ∃ a : ℝ, 0 < a ∧ a < 1 ∧ a * c < 1 := by
  let a : ℝ := 1 / (2 * (c + 1))
  have hd : 0 < 2 * (c + 1) := by positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have he : a * (c + 1) = 1 / 2 := by
    dsimp [a]
    field_simp
  refine ⟨a, ha, ?_, ?_⟩ <;> nlinarith

/-- Negative powers of the dyadic gaps form a geometric sequence. -/
theorem c17_dyadic_gap_rpow (p : ℝ) (n : ℕ) :
    Real.rpow ((1 / 4 : ℝ) * (1 / 2 : ℝ) ^ n) (-p) =
      Real.rpow 4 p * Real.rpow 2 p ^ n := by
  simp only [Real.rpow_eq_pow]
  rw [Real.mul_rpow (by norm_num) (by positivity)]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  rw [mul_comm (n : ℝ) (-p), Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  rw [Real.rpow_natCast, Real.rpow_neg_eq_inv_rpow, Real.rpow_neg_eq_inv_rpow]
  norm_num

/-- Factor the Young error into the force, gap and normalization terms. -/
theorem c17_interpolation_error_factor (θ m K M d g : ℝ)
    (hθ : 0 < θ) (hK : 0 ≤ K) (hM : 0 ≤ M) (hd : 0 < d) (hg : 0 < g) :
    Real.rpow (K * Real.rpow g (-m) * Real.rpow M θ / d) (1 / θ) =
      Real.rpow K (1 / θ) * Real.rpow g (-m / θ) * M / Real.rpow d (1 / θ) := by
  simp only [Real.rpow_eq_pow]
  rw [Real.div_rpow (by positivity) hd.le, Real.mul_rpow (by positivity) (Real.rpow_nonneg hM _),
    Real.mul_rpow hK (Real.rpow_nonneg hg.le _), ← Real.rpow_mul hg.le,
    ← Real.rpow_mul hM]
  have he : θ * (1 / θ) = 1 := by field_simp
  rw [he, Real.rpow_one]
  simp only [div_eq_mul_inv, one_mul]

/-- A bounded local maximum satisfying the interpolation estimate is absorbed uniformly. -/
theorem c17_local_max_interpolation_absorption
    (θ m : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : ℝ → ℝ) (K M T : ℝ),
      0 < K → 0 ≤ M → 0 ≤ T →
      (∀ r ∈ Set.Icc (1/2 : ℝ) 1, 0 ≤ F r ∧ F r ≤ T) →
      (∀ s ∈ Set.Icc (1/2 : ℝ) 1, ∀ t ∈ Set.Icc (1/2 : ℝ) 1, s < t →
        F s ≤ K * Real.rpow (t-s) (-m) * Real.rpow (F t) (1-θ) * Real.rpow M θ) →
      F (1/2) ≤ C * Real.rpow K (1/θ) * M := by
  let c : ℝ := Real.rpow 2 (m / θ)
  have hc : 0 < c := Real.rpow_pos_of_pos (by norm_num) _
  obtain ⟨a, ha, ha1, hac⟩ := c17_absorption_factor c hc.le
  let d : ℝ := Real.rpow (a / (1 - θ)) (1 - θ)
  have hd : 0 < d := Real.rpow_pos_of_pos (div_pos ha (by linarith)) _
  let B : ℝ := θ * Real.rpow 4 (m / θ) / Real.rpow d (1 / θ)
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B * (1 - a * c)⁻¹, mul_pos hB (inv_pos.mpr (by linarith)), ?_⟩
  intro F K M T hK hM hT hF hstep
  let r : ℕ → ℝ := fun n => 1 - (1 / 2 : ℝ) ^ (n + 1)
  have hr : ∀ n, r n ∈ Set.Icc (1/2 : ℝ) 1 := by
    intro n
    exact ⟨(c17_dyadic_radii n).1, (c17_dyadic_radii n).2.1⟩
  have hgap : ∀ n, r (n + 1) - r n = (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ n := by
    intro n
    simpa only [r, Nat.add_assoc] using (c17_dyadic_radii n).2.2.1
  have hgap_pos : ∀ n, 0 < r (n + 1) - r n := by
    intro n
    rw [hgap n]
    exact (c17_dyadic_radii n).2.2.2
  let b : ℝ := B * Real.rpow K (1 / θ) * M
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hrec : ∀ n, F (r n) ≤ a * F (r (n + 1)) + b * c ^ n := by
    intro n
    have h0 := hstep (r n) (hr n) (r (n + 1)) (hr (n + 1)) (sub_pos.mp (hgap_pos n))
    have hY := c17_scaled_interpolation_young θ a
      (K * Real.rpow (r (n + 1) - r n) (-m) * Real.rpow M θ)
      (F (r (n + 1))) hθ hθ1 ha
      (mul_nonneg (mul_nonneg hK.le (Real.rpow_nonneg (hgap_pos n).le _))
        (Real.rpow_nonneg hM _)) (hF _ (hr _)).1
    have hf := c17_interpolation_error_factor θ m K M d (r (n + 1) - r n)
      hθ hK.le hM hd (hgap_pos n)
    have hg := c17_dyadic_gap_rpow (m / θ) n
    rw [hgap n] at hf
    have he : Real.rpow ((1 / 4 : ℝ) * (1 / 2 : ℝ) ^ n) (-m / θ) =
        Real.rpow 4 (m / θ) * Real.rpow 2 (m / θ) ^ n := by
      convert hg using 1; congr 1; ring
    rw [he] at hf
    dsimp [d] at hf
    rw [hgap n] at hY h0
    simp only [Real.rpow_eq_pow] at hf hY h0
    rw [hf] at hY
    have h0' : F (r n) ≤ K * ((1 / 4 : ℝ) * (1 / 2 : ℝ) ^ n) ^ (-m) *
        M ^ θ * F (r (n + 1)) ^ (1 - θ) := by
      convert h0 using 1; ring
    have ht := h0'.trans hY
    dsimp [b, B, c, d]
    convert ht using 1; ring
  have hiter := c17_bounded_additive_geometric_iteration a b c T ha.le ha1 hb hc.le hac
    (fun n => F (r n)) (fun n => (hF _ (hr n)).2) hrec
  rw [tsum_geometric_of_lt_one (mul_nonneg ha.le hc.le) hac] at hiter
  have hstart : r 0 = (1 / 2 : ℝ) := by norm_num [r]
  rw [hstart] at hiter
  dsimp [b] at hiter
  calc
    F (1 / 2) ≤ (B * Real.rpow K (1 / θ) * M) * (1 - a * c)⁻¹ := hiter
    _ = B * (1 - a * c)⁻¹ * Real.rpow K (1 / θ) * M := by ring

end EinsteinFull.Calculus
