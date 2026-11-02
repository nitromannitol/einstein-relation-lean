import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.SpecificLimits.Basic

open MeasureTheory Filter
open scoped Topology

namespace EinsteinFull.Calculus

/-- Remove a positive constant regularization from an almost everywhere bound. -/
theorem c9_harnack_epsilon_removal
 {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
 (μ : Measure X) (ν : Measure Y) (u : X → ℝ) (v : Y → ℝ)
 (q C : ℝ)
 (hu : AEStronglyMeasurable u μ) (hu0 : ∀ᵐ x ∂μ, 0 ≤ u x)
 (hregularized : ∀ n : ℕ, ∀ᵐ y ∂ν,
   eLpNorm (fun x => u x + (1/(n+1 : ℝ))) (ENNReal.ofReal q) μ ≤
   ENNReal.ofReal C * ENNReal.ofReal (v y + (1/(n+1 : ℝ)))) :
 ∀ᵐ y ∂ν, eLpNorm u (ENNReal.ofReal q) μ ≤ ENNReal.ofReal C * ENNReal.ofReal (v y) := by
  have hmono (n : ℕ) : eLpNorm u (ENNReal.ofReal q) μ ≤
      eLpNorm (fun x => u x + (1/(n+1 : ℝ))) (ENNReal.ofReal q) μ := by
    apply eLpNorm_mono_ae_real hu
    filter_upwards [hu0] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg hx]
    exact le_add_of_nonneg_right
      (div_nonneg zero_le_one (add_nonneg (Nat.cast_nonneg n) zero_le_one))
  filter_upwards [ae_all_iff.mpr hregularized] with y hy
  have ht : Tendsto (fun n : ℕ => ENNReal.ofReal C *
      ENNReal.ofReal (v y + (1/(n+1 : ℝ)))) atTop
      (𝓝 (ENNReal.ofReal C * ENNReal.ofReal (v y))) := by
    apply (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).tendsto _ |>.comp
    apply ENNReal.tendsto_ofReal
    simpa only [add_zero] using
      (tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  exact ge_of_tendsto ht (Eventually.of_forall fun n => (hmono n).trans (hy n))

end EinsteinFull.Calculus
