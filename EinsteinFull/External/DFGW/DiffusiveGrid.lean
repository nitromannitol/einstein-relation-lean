import EinsteinFull.External.DFGW.MartingaleTimeRounding
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Diffusive integer grids

The integer part of the inverse squared scale diverges, and its square-root normalization is
asymptotic to the inverse scale.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace EinsteinFull.External.DFGW

/-- The index corresponding to the integer part of the inverse squared scale. -/
noncomputable def diffusiveGridIndex (ε : ℝ) : ℕ := ⌊ε⁻¹ ^ 2⌋₊ - 1

/-- The diffusive grid index tends to infinity as the scale tends to zero from above. -/
theorem tendsto_diffusiveGridIndex : Tendsto diffusiveGridIndex (𝓝[>] 0) atTop := by
  have hinv : Tendsto (fun ε : ℝ => ε⁻¹) (𝓝[>] 0) atTop := tendsto_inv_nhdsGT_zero
  have hsq : Tendsto (fun ε : ℝ => ε⁻¹ ^ 2) (𝓝[>] 0) atTop := by
    simpa only [pow_two] using hinv.atTop_mul_atTop₀ hinv
  exact (tendsto_sub_atTop_nat 1).comp ((tendsto_nat_floor_atTop (α := ℝ)).comp hsq)

/-- The rounded inverse squared scale has the correct square-root normalization. -/
theorem tendsto_diffusiveFloor_sqrt :
    Tendsto (fun ε : ℝ => ε * Real.sqrt (⌊ε⁻¹ ^ 2⌋₊ : ℝ)) (𝓝[>] 0) (𝓝 1) := by
  have hinv : Tendsto (fun ε : ℝ => ε⁻¹) (𝓝[>] 0) atTop := tendsto_inv_nhdsGT_zero
  have hsq : Tendsto (fun ε : ℝ => ε⁻¹ ^ 2) (𝓝[>] 0) atTop := by
    simpa only [pow_two] using hinv.atTop_mul_atTop₀ hinv
  have hratio := (tendsto_nat_floor_div_atTop (R := ℝ)).comp hsq
  have hroot := (Real.continuous_sqrt.tendsto 1).comp hratio
  simp only [Real.sqrt_one] at hroot
  apply hroot.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have he : 0 < ε := hε
  simp only [Function.comp_apply]
  rw [Real.sqrt_div (Nat.cast_nonneg _), Real.sqrt_sq_eq_abs, abs_of_pos (inv_pos.mpr he)]
  field_simp

end EinsteinFull.External.DFGW
