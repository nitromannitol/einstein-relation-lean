import EinsteinFull.External.Source.GMPDirichletKernel
import EinsteinRelation.Correctors.PairedPDECoercivity

namespace EinsteinFull.Calculus
open EinsteinRelation EinsteinFull.External.Source.GMP
open EinsteinRelation.Environment.AKMTestIntegralSupport

/-- The negative half-power gradient is controlled by the elliptic energy. -/
theorem c20_negative_power_coercive_gradient {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (x : Vec d) (v p : ℝ) (hv : 0 < v) (hp : 0 < p) (g : Vec d) :
    (4 * κ * (p+1) / p) * euclideanSq ((-p/2 * Real.rpow v (-p/2-1)) • g) ≤
      p*(p+1)*Real.rpow v (-p-2) * dot ((α x).mulVec g) g := by
  have he := ((hell.2.2 x).2.2.2 g).1
  change κ * euclideanSq g ≤ dotProduct g ((α x).mulVec g) at he
  rw [dotProduct_comm] at he
  change κ * euclideanSq g ≤ dot ((α x).mulVec g) g at he
  have hr : Real.rpow v (-p/2-1) ^ 2 = Real.rpow v (-p-2) := by
    calc
      _ = v ^ ((-p/2-1) + (-p/2-1)) := by
        rw [pow_two]
        exact (Real.rpow_add hv _ _).symm
      _ = _ := by congr 1; ring
  rw [euclideanSq_smul, mul_pow, hr]
  have hrpos : 0 < Real.rpow v (-p-2) := Real.rpow_pos_of_pos hv _
  have hc : 0 ≤ p * (p+1) * Real.rpow v (-p-2) := by positivity
  have hm := mul_le_mul_of_nonneg_left he hc
  have hpne : p ≠ 0 := ne_of_gt hp
  convert hm using 1; field_simp; ring

/-- A symmetric elliptic matrix controls its mixed Euclidean pairing. -/
theorem c20_elliptic_mixed_sq {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (x g z : Vec d) :
    dot ((α x).mulVec g) z ^ 2 ≤
      κ⁻¹ ^ 3 * dot ((α x).mulVec g) g * euclideanSq z := by
  have hsym := (hell.2.2 x).2.2.1
  have hlow (w : Vec d) := ((hell.2.2 x).2.2.2 w).1
  have hupp (w : Vec d) := ((hell.2.2 x).2.2.2 w).2
  have hop := EinsteinRelation.Correctors.mulVec_euclideanNorm_le_of_quadratic
    (α x) (inv_pos.mpr hκ) hsym
    (fun w => (mul_nonneg hκ.le (euclideanSq_nonneg_fisher w)).trans (hlow w))
    hupp g
  have hs : euclideanSq ((α x).mulVec g) ≤ κ⁻¹ ^ 2 * euclideanSq g := by
    have h := (sq_le_sq₀ (Real.sqrt_nonneg _)
      (mul_nonneg (inv_nonneg.mpr hκ.le) (Real.sqrt_nonneg _))).2 hop
    simpa only [euclideanNorm, mul_pow, Real.sq_sqrt (euclideanSq_nonneg_fisher _)] using h
  have hcs : dot ((α x).mulVec g) z ^ 2 ≤
      euclideanSq ((α x).mulVec g) * euclideanSq z := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ ((α x).mulVec g) z
    simpa only [euclideanSq, dot, sq] using h
  have hscaled := mul_le_mul_of_nonneg_right hs (euclideanSq_nonneg_fisher z)
  have he := mul_le_mul_of_nonneg_left (hlow g)
    (mul_nonneg (pow_nonneg (inv_nonneg.mpr hκ.le) 3) (euclideanSq_nonneg_fisher z))
  have hκne : κ ≠ 0 := ne_of_gt hκ
  have heq : κ⁻¹ ^ 2 * euclideanSq g * euclideanSq z =
      (κ⁻¹ ^ 3 * euclideanSq z) * (κ * euclideanSq g) := by
    field_simp
  rw [heq] at hscaled
  calc
    _ ≤ euclideanSq ((α x).mulVec g) * euclideanSq z := hcs
    _ ≤ (κ⁻¹ ^ 3 * euclideanSq z) * (κ * euclideanSq g) := hscaled
    _ ≤ (κ⁻¹ ^ 3 * euclideanSq z) * dot g ((α x).mulVec g) := he
    _ = _ := by
      change (κ⁻¹ ^ 3 * euclideanSq z) * dotProduct g ((α x).mulVec g) = _
      rw [dotProduct_comm]
      change (κ⁻¹ ^ 3 * euclideanSq z) * dot ((α x).mulVec g) g = _
      ring

/-- The mixed negative-power cutoff term is absorbed by elliptic energy. -/
theorem c20_negative_power_mixed_cutoff {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (x : Vec d) (v p : ℝ) (hv : 0 < v) (hp : 0 < p) (g : Vec d)
    (chi : ℝ) (z : Vec d) :
    |2*p*Real.rpow v (-p-1)*chi*dot ((α x).mulVec g) z| ≤
      (p*(p+1)/2)*chi^2*Real.rpow v (-p-2)*dot ((α x).mulVec g) g +
      (2*p/(κ^3*(p+1)))*Real.rpow v (-p)*euclideanSq z := by
  have hpow : Real.rpow v (-p-1)^2 = Real.rpow v (-p-2) * Real.rpow v (-p) := by
    rw [pow_two]
    calc
      _ = v ^ ((-p-1)+(-p-1)) := (Real.rpow_add hv _ _).symm
      _ = v ^ ((-p-2)+(-p)) := by congr 1; ring
      _ = _ := Real.rpow_add hv _ _
  have ha : 0 < Real.rpow v (-p-2) := Real.rpow_pos_of_pos hv _
  have hb : 0 < Real.rpow v (-p) := Real.rpow_pos_of_pos hv _
  have hq : 0 ≤ dot ((α x).mulVec g) g := by
    have h := ((hell.2.2 x).2.2.2 g).1
    change κ * euclideanSq g ≤ dotProduct g ((α x).mulVec g) at h
    rw [dotProduct_comm] at h
    exact (mul_nonneg hκ.le (euclideanSq_nonneg_fisher g)).trans h
  have hz := euclideanSq_nonneg_fisher z
  have hmat := c20_elliptic_mixed_sq hκ ρ α hell x g z
  let A : ℝ := (p*(p+1)/2)*chi^2*Real.rpow v (-p-2)*dot ((α x).mulVec g) g
  let B : ℝ := (2*p/(κ^3*(p+1)))*Real.rpow v (-p)*euclideanSq z
  let X : ℝ := 2*p*Real.rpow v (-p-1)*chi*dot ((α x).mulVec g) z
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hs := mul_le_mul_of_nonneg_left hmat (sq_nonneg (2*p*Real.rpow v (-p-1)*chi))
  have hsq : X^2 ≤ 4*A*B := by
    have hid : (2*p*Real.rpow v (-p-1)*chi)^2 *
        (κ⁻¹ ^ 3 * dot ((α x).mulVec g) g * euclideanSq z) = 4*A*B := by
      dsimp [A, B]
      simp only [Real.rpow_eq_pow] at hpow
      rw [mul_pow, mul_pow, mul_pow, hpow]
      field_simp; ring
    calc
      X^2 = (2*p*Real.rpow v (-p-1)*chi)^2 * dot ((α x).mulVec g) z ^ 2 := by
        dsimp [X]; ring
      _ ≤ _ := hs
      _ = _ := hid
  have hs' : X^2 ≤ (A+B)^2 := by nlinarith [sq_nonneg (A-B)]
  have habs : |X| ≤ A+B := (sq_le_sq₀ (abs_nonneg _) (add_nonneg hA hB)).mp (by
    simpa only [sq_abs] using hs')
  exact habs

end EinsteinFull.Calculus
