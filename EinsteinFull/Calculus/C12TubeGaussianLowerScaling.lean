import EinsteinFull.Calculus.C17TubeParabolicScaling
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open EinsteinRelation MeasureTheory EinsteinFull.External.Source.GMP

namespace EinsteinFull.Calculus

/-- A unit-cylinder Gaussian lower estimate transports to a cylinder of radius `r`.
The hypothesis is the estimate for the actual rescaled density; a weighted-density
producer can be used before multiplying by its endpoint density. -/
theorem c12_gaussian_lower_parabolic_transport {d : ℕ}
    (K : ℝ → Vec d → Vec d → ℝ) (y : Vec d)
    (r c C : ℝ) (hr : 0 < r) (hc : 0 < c) (hC : 0 < C)
    (hunit : ∀ s ∈ Set.Icc (1/4 : ℝ) (1/2 : ℝ),
      ∀ x ∈ sourceBall (0 : Vec d) (1/2),
      ∀ z ∈ sourceBall (0 : Vec d) (1/2),
        c * s ^ (-(d : ℝ)/2) * Real.exp (-C * euclideanSq (z-x) / s)
          ≤ r^d * K (r^2*s) (y+r • x) (y+r • z)) :
    ∀ t ∈ Set.Icc (r^2/4) (r^2/2),
      ∀ a ∈ sourceBall y (r/2), ∀ b ∈ sourceBall y (r/2),
        c * t ^ (-(d : ℝ)/2) * Real.exp (-C * euclideanSq (b-a) / t)
          ≤ K t a b := by
  intro t ht a ha b hb
  let s := t / r^2
  let x := r⁻¹ • (a-y)
  let z := r⁻¹ • (b-y)
  have hr2 : 0 < r^2 := sq_pos_of_pos hr
  have hs : s ∈ Set.Icc (1/4 : ℝ) (1/2 : ℝ) := by
    constructor
    · dsimp [s]; apply (le_div_iff₀ hr2).2; nlinarith [ht.1]
    · dsimp [s]; apply (div_le_iff₀ hr2).2; nlinarith [ht.2]
  have hf (v : Vec d) : y + r • (r⁻¹ • (v-y)) = v := by
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul, add_sub_cancel]
  have hx : x ∈ sourceBall (0 : Vec d) (1/2) := by
    have h := ha
    change euclideanNorm (a-y) < r/2 at h
    change euclideanNorm (x-0) < 1/2
    simp only [sub_zero, x, TimeChange.euclideanNorm_smul, abs_of_pos (inv_pos.mpr hr)]
    rw [inv_mul_eq_div]
    apply (div_lt_iff₀ hr).2
    linarith
  have hz : z ∈ sourceBall (0 : Vec d) (1/2) := by
    have h := hb
    change euclideanNorm (b-y) < r/2 at h
    change euclideanNorm (z-0) < 1/2
    simp only [sub_zero, z, TimeChange.euclideanNorm_smul, abs_of_pos (inv_pos.mpr hr)]
    rw [inv_mul_eq_div]
    apply (div_lt_iff₀ hr).2
    linarith
  have htime : r^2 * s = t := by dsimp [s]; field_simp
  have hdiff : b-a = r • (z-x) := by
    rw [smul_sub, ← hf b, ← hf a]
    simp only [z, x, add_sub_add_left_eq_sub]
  have hsq : euclideanSq (b-a) = r^2 * euclideanSq (z-x) := by
    rw [hdiff]
    simp only [euclideanSq, dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hexp : -C * euclideanSq (b-a) / t = -C * euclideanSq (z-x) / s := by
    rw [hsq, ← htime]
    field_simp
  have hp : (r^2 : ℝ) ^ (-(d : ℝ)/2) = (r^d)⁻¹ := by
    rw [← Real.rpow_natCast r d, ← Real.rpow_neg hr.le, ← Real.rpow_two r,
      ← Real.rpow_mul hr.le]
    congr 1
    ring
  have htpos : 0 < t := by nlinarith [ht.1]
  have hpow : t ^ (-(d : ℝ)/2) = (r^d)⁻¹ * s ^ (-(d : ℝ)/2) := by
    rw [← htime, Real.mul_rpow hr2.le (by dsimp [s]; positivity), hp]
  have hu := hunit s hs x hx z hz
  rw [htime, hf a, hf b] at hu
  rw [hpow, hexp]
  have hrd : 0 < r^d := pow_pos hr d
  have hh := mul_le_mul_of_nonneg_left hu (inv_nonneg.mpr hrd.le)
  convert hh using 1 <;> field_simp [hrd.ne']

end EinsteinFull.Calculus
