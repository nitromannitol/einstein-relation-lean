import EinsteinFull.Blueprint.G3.node_e_u3A_clock_u2D_early
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation
theorem clock_early_force_window
    : ∀ (t₀ C₀ : ℝ), 1 ≤ t₀ → 0 < C₀ →
      ∃ T₀ : ℝ, 625 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
        let τ := T ^ (1 - (1 / 4 : ℝ))
        t₀ ≤ τ ∧ 5 * τ ≤ T ∧ ∀ ζ : ℂ,
          (‖ζ‖ * Real.sqrt T ≤ 2 ∨ ∃ x : ℝ, ζ = (x : ℂ) ∧
            |x| * Real.sqrt T ≤ C₀ * Real.log T ^ (1 / 4 : ℝ)) →
          ‖ζ‖ * Real.sqrt τ ≤ 1 := by
  intro t₀ C₀ _ht₀ _hC₀
  have hlog := ((isLittleO_log_rpow_rpow_atTop (1 / 4 : ℝ)
    (show (0 : ℝ) < 1 / 8 by norm_num)).const_mul_left C₀).eventuallyLE
  have hlarge : ∀ᶠ T : ℝ in atTop,
      625 ≤ T ∧ t₀ ≤ T ^ (3 / 4 : ℝ) ∧ 5 ≤ T ^ (1 / 4 : ℝ) ∧
      2 ≤ T ^ (1 / 8 : ℝ) ∧ C₀ * Real.log T ^ (1 / 4 : ℝ) ≤ T ^ (1 / 8 : ℝ) := by
    filter_upwards [eventually_ge_atTop (625 : ℝ),
      (tendsto_rpow_atTop (show (0 : ℝ) < 3 / 4 by norm_num)).eventually_ge_atTop t₀,
      (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 4 by norm_num)).eventually_ge_atTop 5,
      (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 8 by norm_num)).eventually_ge_atTop 2,
      hlog] with T hT ht h5 h2 hl
    refine ⟨hT, ht, h5, h2, ?_⟩
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (show 0 ≤ T by linarith) _)] at hl
    exact (le_abs_self _).trans hl
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 hlarge
  refine ⟨max 625 T₀, le_max_left _ _, ?_⟩
  intro T hT
  obtain ⟨h625, ht, h5, h2, hl⟩ := hT₀ T ((le_max_right _ _).trans hT)
  have hpos : 0 < T := by linarith
  dsimp only
  rw [show (1 - (1 / 4 : ℝ)) = 3 / 4 by norm_num]
  refine ⟨ht, ?_, ?_⟩
  · calc
      5 * T ^ (3 / 4 : ℝ) ≤ T ^ (1 / 4 : ℝ) * T ^ (3 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_right h5 (Real.rpow_nonneg hpos.le _)
      _ = T := by rw [← Real.rpow_add hpos]; norm_num
  · have hid : Real.sqrt (T ^ (3 / 4 : ℝ)) * T ^ (1 / 8 : ℝ) = Real.sqrt T := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hpos.le, ← Real.rpow_add hpos]
      norm_num [Real.sqrt_eq_rpow]
    intro ζ hζ
    have hb : ‖ζ‖ * Real.sqrt T ≤ T ^ (1 / 8 : ℝ) := by
      rcases hζ with hc | ⟨x, rfl, hx⟩
      · exact hc.trans h2
      · simpa only [Complex.norm_real, Real.norm_eq_abs] using hx.trans hl
    have hm : (‖ζ‖ * Real.sqrt (T ^ (3 / 4 : ℝ))) * T ^ (1 / 8 : ℝ) ≤
        1 * T ^ (1 / 8 : ℝ) := by
      rw [mul_assoc, hid, one_mul]
      exact hb
    exact (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hpos _)).1 hm
end EinsteinFull.Blueprint
