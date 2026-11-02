import EinsteinFull.Calculus.C5TubeWeightedCaccioppoli
import EinsteinRelation.Environment.AKMTestIntegralSupport

open EinsteinRelation MeasureTheory Filter EinsteinFull.External.Source.GMP
open PDE hiding Vec Mat
open scoped Topology

namespace EinsteinFull.Calculus

/-- The gradient of a positive fractional power inherits elliptic coercivity. -/
theorem c13_small_power_coercive_gradient {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (x : Vec d) (v p : ℝ) (hv : 0 < v) (hp : 0 < p) (hp1 : p < 1)
    (g : Vec d) :
    (4*κ*(1-p)/p) * euclideanSq ((p/2 * Real.rpow v (p/2-1)) • g) ≤
      p*(1-p)*Real.rpow v (p-2) * dot ((α x).mulVec g) g := by
  have hr : (Real.rpow v (p / 2 - 1)) ^ 2 = Real.rpow v (p - 2) := by
    have h := Real.rpow_add hv (p / 2 - 1) (p / 2 - 1)
    have hex : p / 2 - 1 + (p / 2 - 1) = p - 2 := by ring
    rw [hex] at h
    simpa only [Real.rpow_eq_pow, pow_two] using h.symm
  have he := (hell.2.2 x).2.2.2 g |>.1
  have hd : dot g ((α x).mulVec g) = dot ((α x).mulVec g) g := by
    simp only [dot, mul_comm]
  rw [hd] at he
  rw [EinsteinRelation.Environment.AKMTestIntegralSupport.euclideanSq_smul]
  have hp1pos : 0 < 1 - p := by linarith
  have hrpos := Real.rpow_pos_of_pos hv (p-2)
  have hc : 0 ≤ p * (1-p) * Real.rpow v (p-2) := by positivity
  have hs := mul_le_mul_of_nonneg_left he hc
  have hid : (4*κ*(1-p)/p) * ((p/2 * Real.rpow v (p/2-1)) ^ 2 * euclideanSq g) =
      (p*(1-p)*Real.rpow v (p-2)) * (κ * euclideanSq g) := by
    rw [mul_pow, hr]
    field_simp [ne_of_gt hp]
    ring
  rw [hid]
  exact hs

/-- Young absorption for the fractional-power mixed coefficient flux. -/
theorem c13_small_power_mixed_flux_bound {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (x : Vec d) (v p : ℝ) (hv : 0 < v) (hp : 0 < p) (hp1 : p < 1)
    (g : Vec d) (chi : ℝ) (z : Vec d) :
    |2*p*Real.rpow v (p-1)*chi*dot ((α x).mulVec g) z| ≤
      (p*(1-p)/2)*chi^2*Real.rpow v (p-2)*dot ((α x).mulVec g) g +
      (2*p/(κ^3*(1-p)))*Real.rpow v p*euclideanSq z := by
  have hpow : (Real.rpow v (p-1)) ^ 2 = Real.rpow v (p-2) * Real.rpow v p := by
    have h1 := Real.rpow_add hv (p - 1) (p - 1)
    have h2 := Real.rpow_add hv (p - 2) p
    have hex : p - 1 + (p - 1) = p - 2 + p := by ring
    rw [hex, h2] at h1
    simpa only [Real.rpow_eq_pow, pow_two] using h1.symm
  have hp1pos : 0 < 1-p := by linarith
  have hrpos := Real.rpow_pos_of_pos hv (p-2)
  have hrp := Real.rpow_pos_of_pos hv p
  have hk : κ ≤ κ⁻¹ := (hell.2.2 x).1.trans (hell.2.2 x).2.1
  have hk1 : κ ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hk hκ.le
    have hi : κ * κ⁻¹ = 1 := mul_inv_cancel₀ hκ.ne'
    nlinarith [sq_nonneg (κ-1)]
  have hinv : 1 ≤ κ⁻¹ := (one_le_inv₀ hκ).2 hk1
  have hL : κ⁻¹ ≤ (κ^3)⁻¹ := by
    rw [← inv_pow]
    nlinarith [sq_nonneg (κ⁻¹ - 1), mul_nonneg (sub_nonneg.mpr hinv) (sq_nonneg (κ⁻¹))]
  have hq : 0 ≤ dot g ((α x).mulVec g) := by
    exact (mul_nonneg hκ.le (PDE.vecNormSq_nonneg g)).trans ((hell.2.2 x).2.2.2 g).1
  have hcross := c5_weighted_flux_cross_bound hκ hell x g z
  have hc : dot ((α x).mulVec g) z ^ 2 ≤ (κ^3)⁻¹ * dot g ((α x).mulVec g) * euclideanSq z := by
    exact hcross.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hL hq)
      (PDE.vecNormSq_nonneg z))
  have hf : (p * Real.rpow v (p-1)) ^ 2 ≤
      (p/(1-p)) * (p*(1-p)*Real.rpow v (p-2)) * Real.rpow v p := by
    rw [mul_pow, hpow]
    have hp1' : 1-p ≠ 0 := by linarith
    field_simp [hp1']
    ring_nf
    rfl
  have hy := PDE.Parabolic.LocalMax.abs_young_le
    (F0 := Real.rpow v p) (F1 := p * Real.rpow v (p-1))
    (F2 := p*(1-p)*Real.rpow v (p-2)) (K := p/(1-p)) (L := (κ^3)⁻¹)
    (Q := dot g ((α x).mulVec g)) (N := euclideanSq z) (η := chi) (χ := 1)
    (P := dot ((α x).mulVec g) z)
    (by positivity) (by positivity) (by positivity) (by positivity) hq
    (PDE.vecNormSq_nonneg z) (by norm_num) hf hc
  have hd : dot g ((α x).mulVec g) = dot ((α x).mulVec g) g := by
    simp only [dot, mul_comm]
  rw [hd] at hy
  convert hy using 1 <;> (try simp only [div_eq_mul_inv, mul_inv_rev]) <;> ring

end EinsteinFull.Calculus
