import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

noncomputable section

/-- The physical radius and time scales fit a common parabolic envelope. -/
theorem c34_flux_block_good_event_scale_factor
    (t s η : ℝ) (ζ : ℂ) (ht : 1 ≤ t) (hs : 1 ≤ s) (hη : 0 ≤ η) :
    ((t : ℝ)⁻¹ + ‖ζ‖ * (Real.sqrt t)⁻¹ +
        ((Real.sqrt t)⁻¹ + ‖ζ‖) * ((t ^ (1/2 + η))⁻¹ + (Real.sqrt s)⁻¹)) ≤
      6 * t⁻¹ * (1 + ‖ζ‖ * Real.sqrt t) * (1 + t / s) := by
  have htpos : 0 < t := by linarith
  have hspos : 0 < s := by linarith
  have hT : 0 < Real.sqrt t := Real.sqrt_pos.2 htpos
  have hS : 0 < Real.sqrt s := Real.sqrt_pos.2 hspos
  have hT2 : (Real.sqrt t)^2 = t := Real.sq_sqrt (le_of_lt htpos)
  have hS2 : (Real.sqrt s)^2 = s := Real.sq_sqrt (le_of_lt hspos)
  have hr : Real.sqrt t ≤ t ^ (1/2 + η) := by
    rw [Real.rpow_add htpos, ← Real.sqrt_eq_rpow]
    nlinarith [Real.one_le_rpow ht hη]
  have hir : (t ^ (1/2 + η))⁻¹ ≤ (Real.sqrt t)⁻¹ :=
    (inv_le_inv₀ (lt_of_lt_of_le hT hr) hT).2 hr
  have hz : 0 ≤ ‖ζ‖ := norm_nonneg _
  have hts : Real.sqrt t * Real.sqrt s ≤ t + s := by
    nlinarith [sq_nonneg (Real.sqrt t - Real.sqrt s)]
  have hratio : Real.sqrt t * (Real.sqrt s)⁻¹ ≤ 1 + t / s := by
    calc
      Real.sqrt t * (Real.sqrt s)⁻¹ = (Real.sqrt t * Real.sqrt s) / s := by
        field_simp
        nlinarith [congrArg (fun x : ℝ => Real.sqrt t * x) hS2]
      _ ≤ (t + s) / s := div_le_div_of_nonneg_right hts (le_of_lt hspos)
      _ = 1 + t / s := by field_simp; ring
  have hinv : t⁻¹ = (Real.sqrt t)⁻¹ * (Real.sqrt t)⁻¹ := by
    rw [← pow_two, inv_pow, hT2]
  have hfac : 0 ≤ t⁻¹ * (1 + ‖ζ‖ * Real.sqrt t) := by positivity
  have hbound : t⁻¹ + ‖ζ‖ * (Real.sqrt t)⁻¹ +
      ((Real.sqrt t)⁻¹ + ‖ζ‖) * ((Real.sqrt t)⁻¹ + (Real.sqrt s)⁻¹) ≤
      6 * t⁻¹ * (1 + ‖ζ‖ * Real.sqrt t) * (1 + t / s) := by
    have heq : t⁻¹ + ‖ζ‖ * (Real.sqrt t)⁻¹ +
        ((Real.sqrt t)⁻¹ + ‖ζ‖) * ((Real.sqrt t)⁻¹ + (Real.sqrt s)⁻¹) =
        t⁻¹ * (1 + ‖ζ‖ * Real.sqrt t) *
          (2 + Real.sqrt t * (Real.sqrt s)⁻¹) := by
      rw [hinv]
      field_simp
      nlinarith [hT2]
    rw [heq]
    have hp : 0 ≤ t / s := div_nonneg (le_of_lt htpos) (le_of_lt hspos)
    have hh : 2 + Real.sqrt t * (Real.sqrt s)⁻¹ ≤ 6 * (1 + t / s) := by linarith
    calc
      _ ≤ (t⁻¹ * (1 + ‖ζ‖ * Real.sqrt t)) * (6 * (1 + t / s)) :=
        mul_le_mul_of_nonneg_left hh hfac
      _ = _ := by ring
  exact le_trans (by gcongr) hbound
