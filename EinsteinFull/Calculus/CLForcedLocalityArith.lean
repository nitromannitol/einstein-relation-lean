import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.Exponential

/-! Arithmetic for the forced-locality error shape. The retained-family errors
carry polynomial factors in the radius and the time; half of the Gaussian decay
absorbs the radial polynomial, and the remaining factors are polynomial in
`2 + t`. -/

open Real

namespace EinsteinFull

/-- A polynomial is dominated by half of an exponential. -/
theorem clr_one_add_pow_le_exp {a : ℝ} (ha : 0 < a) (n : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    (1 + y) ^ n ≤ n.factorial * (2 / a) ^ n * Real.exp (a / 2) * Real.exp (a / 2 * y) := by
  set x := a / 2 * (1 + y) with hxdef
  have hx : 0 ≤ x := by positivity
  have h := Real.pow_div_factorial_le_exp (x := x) hx n
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have h1 : x ^ n ≤ n.factorial * Real.exp x := by
    rw [div_le_iff₀ hfac] at h; linarith
  have hy1 : (1 + y) = (2 / a) * x := by rw [hxdef]; field_simp
  have hex : Real.exp x = Real.exp (a / 2) * Real.exp (a / 2 * y) := by
    rw [← Real.exp_add, hxdef]; ring_nf
  calc (1 + y) ^ n = (2 / a) ^ n * x ^ n := by rw [hy1, mul_pow]
    _ ≤ (2 / a) ^ n * (n.factorial * Real.exp x) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = n.factorial * (2 / a) ^ n * Real.exp (a / 2) * Real.exp (a / 2 * y) := by
        rw [hex]; ring

/-- `√x ≤ 1 + x` for nonnegative `x`. -/
theorem clr_sqrt_le_one_add {x : ℝ} (hx : 0 ≤ x) : Real.sqrt x ≤ 1 + x := by
  nlinarith [Real.sq_sqrt hx, Real.sqrt_nonneg x]

/-- The Gaussian mass factor of the kernel tail is polynomial in time. -/
theorem clr_mass_factor_le {d : ℕ} {c t : ℝ} (hc : 0 < c) (ht : 1 ≤ t) :
    Real.sqrt (Real.pi / (c / (2 * t))) ^ d ≤ (1 + 2 * Real.pi / c) ^ d * (2 + t) ^ d := by
  have htp : 0 < t := by linarith
  have he : Real.pi / (c / (2 * t)) = 2 * Real.pi / c * t := by field_simp
  have h0 : 0 ≤ 2 * Real.pi / c * t := by positivity
  have hs : Real.sqrt (Real.pi / (c / (2 * t))) ≤ (1 + 2 * Real.pi / c) * (2 + t) := by
    rw [he]
    refine (clr_sqrt_le_one_add h0).trans ?_
    have hp : 0 ≤ 2 * Real.pi / c := by positivity
    nlinarith
  rw [← mul_pow]
  exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hs d

/-- The first retained-family term in Gaussian form. -/
theorem clr_family_term1_le {d n₁ : ℕ} {A₁ C₁ c₁ κ t ρ z : ℝ} (hA₁ : 0 ≤ A₁) (hc₁ : 0 < c₁)
    (ht : 1 ≤ t) :
    A₁ * (2 + t) ^ n₁ * Real.exp (C₁ * z * t) * Real.exp (-(c₁ * (κ * ρ) ^ 2 / (8 * t))) *
        Real.sqrt (Real.pi / (c₁ / (2 * t))) ^ d ≤
      (A₁ * (1 + 2 * Real.pi / c₁) ^ d) * (2 + t) ^ (n₁ + d) *
        Real.exp (C₁ * z * t - (c₁ * κ ^ 2 / 8) * ρ ^ 2 / t) := by
  have hm := clr_mass_factor_le (d := d) hc₁ ht
  have he : Real.exp (C₁ * z * t) * Real.exp (-(c₁ * (κ * ρ) ^ 2 / (8 * t))) =
      Real.exp (C₁ * z * t - (c₁ * κ ^ 2 / 8) * ρ ^ 2 / t) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  have hE : 0 ≤ Real.exp (C₁ * z * t - (c₁ * κ ^ 2 / 8) * ρ ^ 2 / t) := (Real.exp_pos _).le
  calc A₁ * (2 + t) ^ n₁ * Real.exp (C₁ * z * t) * Real.exp (-(c₁ * (κ * ρ) ^ 2 / (8 * t))) *
        Real.sqrt (Real.pi / (c₁ / (2 * t))) ^ d
      = A₁ * (2 + t) ^ n₁ * Real.exp (C₁ * z * t - (c₁ * κ ^ 2 / 8) * ρ ^ 2 / t) *
          Real.sqrt (Real.pi / (c₁ / (2 * t))) ^ d := by rw [mul_assoc (A₁ * _), he]
    _ ≤ A₁ * (2 + t) ^ n₁ * Real.exp (C₁ * z * t - (c₁ * κ ^ 2 / 8) * ρ ^ 2 / t) *
          ((1 + 2 * Real.pi / c₁) ^ d * (2 + t) ^ d) :=
        mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by rw [pow_add]; ring

/-- The second retained-family term in Gaussian form: half of the decay absorbs
the radial volume factor. -/
theorem clr_family_term2_le {d : ℕ} {A₂ C₂ c₂ κ κ' t ρ z : ℝ} (hA₂ : 0 ≤ A₂) (hc₂ : 0 < c₂)
    (hκ : 0 < κ) (ht : 1 ≤ t) :
    A₂ * (2 + t) * Real.exp (C₂ * z * t - c₂ * (κ * ρ) ^ 2 / t) *
        Real.sqrt (Real.exp 1 * Real.sqrt (Real.pi / (1 / (4 * (κ' * ρ) ^ 2))) ^ d) ≤
      (A₂ * (2 * Real.exp 1) * (2 + 4 * Real.pi * κ' ^ 2) ^ d *
          (d.factorial * (2 / (c₂ * κ ^ 2)) ^ d * Real.exp (c₂ * κ ^ 2 / 2))) *
        (2 + t) ^ (1 + d) * Real.exp (C₂ * z * t - (c₂ * κ ^ 2 / 2) * ρ ^ 2 / t) := by
  have htp : 0 < t := by linarith
  set a : ℝ := c₂ * κ ^ 2 with hadef
  have ha : 0 < a := by positivity
  set b : ℝ := 4 * Real.pi * κ' ^ 2 with hbdef
  have hb : 0 ≤ b := by positivity
  set y : ℝ := ρ ^ 2 / t with hydef
  have hy : 0 ≤ y := by positivity
  set s : ℝ := Real.sqrt (Real.pi / (1 / (4 * (κ' * ρ) ^ 2))) with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsle : s ≤ 1 + b * ρ ^ 2 := by
    have he : Real.pi / (1 / (4 * (κ' * ρ) ^ 2)) = b * ρ ^ 2 := by
      rw [hbdef]; field_simp
    rw [hsdef, he]
    exact clr_sqrt_le_one_add (by positivity)
  -- the volume factor
  have hvol : Real.sqrt (Real.exp 1 * s ^ d) ≤ 2 * Real.exp 1 * (1 + s) ^ d := by
    have h1 : Real.sqrt (Real.exp 1 * s ^ d) ≤ 1 + Real.exp 1 * s ^ d :=
      clr_sqrt_le_one_add (by positivity)
    have h2 : s ^ d ≤ (1 + s) ^ d := pow_le_pow_left₀ hs0 (by linarith) d
    have h3 : (1 : ℝ) ≤ (1 + s) ^ d := one_le_pow₀ (by linarith)
    have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    nlinarith
  have hρ2 : ρ ^ 2 = t * y := by rw [hydef]; field_simp
  have hpoly : (1 + s) ^ d ≤ (2 + b) ^ d * (2 + t) ^ d * (1 + y) ^ d := by
    have h1 : 1 + s ≤ (2 + b) * (2 + t) * (1 + y) := by
      have : 1 + s ≤ 2 + b * (t * y) := by rw [← hρ2]; linarith
      nlinarith [mul_nonneg hb (mul_nonneg htp.le hy), mul_nonneg htp.le hy]
    rw [← mul_pow, ← mul_pow]
    exact pow_le_pow_left₀ (by linarith) h1 d
  have hexp := clr_one_add_pow_le_exp ha d hy
  have hsplit : Real.exp (C₂ * z * t - c₂ * (κ * ρ) ^ 2 / t) =
      Real.exp (C₂ * z * t - (a / 2) * ρ ^ 2 / t) * Real.exp (-(a / 2 * y)) := by
    rw [← Real.exp_add]; congr 1; rw [hadef, hydef]; ring
  have hcancel : Real.exp (-(a / 2 * y)) * Real.exp (a / 2 * y) = 1 := by
    rw [← Real.exp_add]; simp
  set Ex := Real.exp (C₂ * z * t - (a / 2) * ρ ^ 2 / t)
  have hEx : 0 ≤ Ex := (Real.exp_pos _).le
  have hcore : Real.exp (-(a / 2 * y)) * (1 + y) ^ d ≤
      d.factorial * (2 / a) ^ d * Real.exp (a / 2) := by
    calc Real.exp (-(a / 2 * y)) * (1 + y) ^ d
        ≤ Real.exp (-(a / 2 * y)) *
          (d.factorial * (2 / a) ^ d * Real.exp (a / 2) * Real.exp (a / 2 * y)) :=
          mul_le_mul_of_nonneg_left hexp (Real.exp_pos _).le
      _ = d.factorial * (2 / a) ^ d * Real.exp (a / 2) *
          (Real.exp (-(a / 2 * y)) * Real.exp (a / 2 * y)) := by ring
      _ = d.factorial * (2 / a) ^ d * Real.exp (a / 2) := by rw [hcancel, mul_one]
  calc A₂ * (2 + t) * Real.exp (C₂ * z * t - c₂ * (κ * ρ) ^ 2 / t) *
        Real.sqrt (Real.exp 1 * s ^ d)
      ≤ A₂ * (2 + t) * Real.exp (C₂ * z * t - c₂ * (κ * ρ) ^ 2 / t) *
          (2 * Real.exp 1 * ((2 + b) ^ d * (2 + t) ^ d * (1 + y) ^ d)) := by
        apply mul_le_mul_of_nonneg_left (hvol.trans _) (by positivity)
        exact mul_le_mul_of_nonneg_left hpoly (by positivity)
    _ = A₂ * (2 * Real.exp 1) * (2 + b) ^ d * ((2 + t) * (2 + t) ^ d) * Ex *
          (Real.exp (-(a / 2 * y)) * (1 + y) ^ d) := by rw [hsplit]; ring
    _ ≤ A₂ * (2 * Real.exp 1) * (2 + b) ^ d * ((2 + t) * (2 + t) ^ d) * Ex *
          (d.factorial * (2 / a) ^ d * Real.exp (a / 2)) :=
        mul_le_mul_of_nonneg_left hcore (by positivity)
    _ = _ := by rw [pow_add, pow_one]; ring

/-- Two Gaussian-form terms are dominated by one. -/
theorem clr_two_gaussian_le {K₁ K₂ C₁ C₂ c₁ c₂ t ρ z : ℝ} {N₁ N₂ : ℕ} (hK₁ : 0 ≤ K₁)
    (hK₂ : 0 ≤ K₂) (ht : 1 ≤ t) (hz : 0 ≤ z) :
    K₁ * (2 + t) ^ N₁ * Real.exp (C₁ * z * t - c₁ * ρ ^ 2 / t) +
        K₂ * (2 + t) ^ N₂ * Real.exp (C₂ * z * t - c₂ * ρ ^ 2 / t) ≤
      (K₁ + K₂) * (2 + t) ^ (max N₁ N₂) *
        Real.exp (max C₁ C₂ * z * t - min c₁ c₂ * ρ ^ 2 / t) := by
  have htp : 0 < t := by linarith
  have hb : (1 : ℝ) ≤ 2 + t := by linarith
  have hp1 : (2 + t) ^ N₁ ≤ (2 + t) ^ (max N₁ N₂) := pow_le_pow_right₀ hb (le_max_left _ _)
  have hp2 : (2 + t) ^ N₂ ≤ (2 + t) ^ (max N₁ N₂) := pow_le_pow_right₀ hb (le_max_right _ _)
  have hzt : 0 ≤ z * t := by positivity
  have hρt : 0 ≤ ρ ^ 2 / t := by positivity
  have he (C c : ℝ) (hC : C ≤ max C₁ C₂) (hc : min c₁ c₂ ≤ c) :
      Real.exp (C * z * t - c * ρ ^ 2 / t) ≤
        Real.exp (max C₁ C₂ * z * t - min c₁ c₂ * ρ ^ 2 / t) := by
    apply Real.exp_le_exp.mpr
    have h1 : C * (z * t) ≤ max C₁ C₂ * (z * t) := mul_le_mul_of_nonneg_right hC hzt
    have h2 : min c₁ c₂ * (ρ ^ 2 / t) ≤ c * (ρ ^ 2 / t) := mul_le_mul_of_nonneg_right hc hρt
    have e1 : C * z * t - c * ρ ^ 2 / t = C * (z * t) - c * (ρ ^ 2 / t) := by ring
    have e2 : max C₁ C₂ * z * t - min c₁ c₂ * ρ ^ 2 / t =
        max C₁ C₂ * (z * t) - min c₁ c₂ * (ρ ^ 2 / t) := by ring
    rw [e1, e2]; linarith
  have h1 := he C₁ c₁ (le_max_left _ _) (min_le_left _ _)
  have h2 := he C₂ c₂ (le_max_right _ _) (min_le_right _ _)
  set E := Real.exp (max C₁ C₂ * z * t - min c₁ c₂ * ρ ^ 2 / t)
  have hE : 0 ≤ E := (Real.exp_pos _).le
  calc K₁ * (2 + t) ^ N₁ * Real.exp (C₁ * z * t - c₁ * ρ ^ 2 / t) +
        K₂ * (2 + t) ^ N₂ * Real.exp (C₂ * z * t - c₂ * ρ ^ 2 / t)
      ≤ K₁ * (2 + t) ^ (max N₁ N₂) * E + K₂ * (2 + t) ^ (max N₁ N₂) * E := by
        gcongr
    _ = (K₁ + K₂) * (2 + t) ^ (max N₁ N₂) * E := by ring

end EinsteinFull
