import EinsteinRelation.Correctors.CoordinateFieldMomentBounds

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace EinsteinRelation.Correctors

/-- Convert a positive real moment to an explicit norm bound
(`paper/main.tex:710–719,1070–1082`). -/
theorem eLpNorm_le_of_lintegral_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {m C : ℝ} (hm : 0 < m) {f : Ω → ℝ}
    (hf : ∀ ω, 0 ≤ f ω)
    (hb : (∫⁻ ω, ENNReal.ofReal ((f ω) ^ m) ∂μ) ≤ ENNReal.ofReal C) :
    eLpNorm f (ENNReal.ofReal m) μ ≤ ENNReal.ofReal ((max C 0) ^ (1 / m)) := by
  have hm0 : ENNReal.ofReal m ≠ 0 := (ENNReal.ofReal_pos.mpr hm).ne'
  have hm_top : ENNReal.ofReal m ≠ ∞ := ENNReal.ofReal_ne_top
  rw [eLpNorm_eq_lintegral_rpow_enorm hm0 hm_top, ENNReal.toReal_ofReal hm.le]
  have h_enorm_pow (ω : Ω) : ‖f ω‖ₑ ^ m = ENNReal.ofReal ((f ω) ^ m) := by
    rw [Real.enorm_of_nonneg (hf ω), ENNReal.ofReal_rpow_of_nonneg (hf ω) hm.le]
  simp_rw [h_enorm_pow]
  have hpos : 0 ≤ 1 / m := div_nonneg (by norm_num) hm.le
  refine (ENNReal.rpow_le_rpow hb hpos).trans ?_
  by_cases hC : 0 ≤ C
  · have h_exp_nonneg : 0 ≤ 1 / m := div_nonneg (by norm_num) hm.le
    rw [ENNReal.ofReal_rpow_of_nonneg hC h_exp_nonneg]
    simp [hC]
  · have hC' : C ≤ 0 := by linarith
    have hmax : max C 0 = 0 := by simp [hC']
    have hCzero : ENNReal.ofReal C = 0 := ENNReal.ofReal_eq_zero.mpr hC'
    have hzero_pow : ENNReal.ofReal ((0 : ℝ) ^ (1 / m)) = 0 := by
      rw [Real.zero_rpow (div_pos (by norm_num) hm).ne', ENNReal.ofReal_zero]
    rw [hmax, hzero_pow, hCzero, ENNReal.zero_rpow_of_pos (div_pos (by norm_num) hm)]

end EinsteinRelation.Correctors
