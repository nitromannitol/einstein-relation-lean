import EinsteinFull.External.DFGW.MartingaleTimeRounding
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Diffusive grid scales

The inverse square root of an integer grid parameter is a positive scale tending to zero,
and its inverse square is the grid parameter.
-/

open MeasureTheory Filter
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

/-- The scale associated with row `n` of the diffusive grid. -/
noncomputable def gridScale (n : ℕ) : ℝ := (Real.sqrt (n + 1))⁻¹

/-- Diffusive grid scales tend to zero from above. -/
theorem tendsto_gridScale : Tendsto gridScale atTop (𝓝[>] 0) := by
  have hn : Tendsto (fun n : ℕ => (n + 1 : ℝ)) atTop atTop := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hs := Real.tendsto_sqrt_atTop.comp hn
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · exact tendsto_inv_atTop_zero.comp hs
  · exact Eventually.of_forall fun n => inv_pos.mpr (Real.sqrt_pos.2 (by positivity))

/-- The inverse square of a grid scale is the corresponding integer grid parameter. -/
theorem gridScale_inv_sq (n : ℕ) : (gridScale n)⁻¹ ^ 2 = (n + 1 : ℝ) := by
  simp only [gridScale, inv_inv, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n + 1)]

/-- Rounding a scaled time at a grid scale agrees with taking its integer part. -/
theorem floorTime_gridScale (n : ℕ) (t : ℝ≥0) :
    floorTime (((gridScale n)⁻¹ ^ 2).toNNReal * t) =
      (⌊(t : ℝ) * (n + 1 : ℝ)⌋₊ : ℝ≥0) := by
  rw [gridScale_inv_sq]
  simp only [floorTime, NNReal.coe_mul, Real.coe_toNNReal (n + 1 : ℝ) (by positivity), mul_comm]

end EinsteinFull.External.DFGW
