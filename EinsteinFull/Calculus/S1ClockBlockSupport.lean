import EinsteinFull.Blueprint.G3.LocalizedCovarianceObjects
import EinsteinFull.Work.W7.ClockFiniteRangeSupport

/-! The clock coordinate of the localized covariance field uses the ISOTROPIC source
kernel `heatKernel 0 r` (variance `2 r²` per coordinate), which is the anisotropic
Gaussian with matrix `2 • 1` and scale `r²`. The block estimates of the finite-range clock
therefore apply with `A = 2 • 1`, truncation set `ball 0 ρ`. -/

open MeasureTheory

namespace EinsteinFull.Calculus.S1
open EinsteinFull EinsteinRelation EinsteinRelation.External.AKM

variable {d : ℕ}

theorem two_smul_one_posDef : ((2 : ℝ) • (1 : Mat d)).PosDef := by
  have h : (1 : Mat d).PosDef := Matrix.PosDef.one
  exact h.smul (by norm_num)

theorem heatKernel_eq_anisotropic (r : ℝ) (hr : 0 < r) :
    heatKernel (0 : Vec d) r = anisotropicGaussian ((2 : ℝ) • (1 : Mat d)) (r ^ 2) := by
  funext z
  have hinv : ((2 : ℝ) • (1 : Mat d))⁻¹ = (2 : ℝ)⁻¹ • (1 : Mat d) := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ (by norm_num), one_smul]
  have hdet : ((2 : ℝ) • (1 : Mat d)).det = 2 ^ d := by
    rw [Matrix.det_smul, Matrix.det_one]
    simp
  have hsum : ∑ j, ∑ k, z j * ((2 : ℝ)⁻¹ • (1 : Mat d)) j k * z k = 2⁻¹ * euclideanSq z := by
    simp only [euclideanSq, dot, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite,
      mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  unfold heatKernel Correctors.euclideanHeatKernel anisotropicGaussian
  rw [hinv, hdet, hsum, sub_zero]
  have hr2 : 0 < r ^ 2 := by positivity
  have h4 : (4 * Real.pi * r ^ 2) = (2 * Real.pi * r ^ 2) * 2 := by ring
  have hsq : Real.sqrt ((2 : ℝ) ^ d) = (2 : ℝ) ^ ((d : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (2 : ℝ) d, ← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  rw [h4, Real.mul_rpow (by positivity) (by norm_num), hsq]
  have hneg : (2 : ℝ) ^ (-(d : ℝ) / 2) = ((2 : ℝ) ^ ((d : ℝ) / 2))⁻¹ := by
    rw [← Real.rpow_neg (by norm_num)]
    congr 1
    ring
  rw [hneg]
  have hexp : -euclideanSq z / (4 * r ^ 2) = -(2⁻¹ * euclideanSq z) / (2 * r ^ 2) := by
    field_simp
    ring
  rw [hexp]
  have hpos : 0 < (2 : ℝ) ^ ((d : ℝ) / 2) := Real.rpow_pos_of_pos (by norm_num) _
  field_simp

theorem rpow_neg_half_sq_mul_pow {L : ℝ} (hL : 0 < L) (d : ℕ) :
    (L ^ (-(d : ℝ) / 2)) ^ 2 * L ^ d = 1 := by
  rw [← Real.rpow_natCast (L ^ (-(d : ℝ) / 2)) 2, ← Real.rpow_mul hL.le,
    ← Real.rpow_natCast L d, ← Real.rpow_add hL]
  have : -(d : ℝ) / 2 * ((2 : ℕ) : ℝ) + (d : ℝ) = 0 := by push_cast; ring
  rw [this, Real.rpow_zero]

theorem measurableSet_ball_zero (ρ : ℝ) : MeasurableSet (ball (0 : Vec d) ρ) := by
  have : ball (0 : Vec d) ρ = {z : Vec d | euclideanNorm z < ρ} := by
    ext z
    simp [ball]
  rw [this]
  apply measurableSet_lt _ measurable_const
  unfold euclideanNorm euclideanSq dot
  fun_prop

end EinsteinFull.Calculus.S1
