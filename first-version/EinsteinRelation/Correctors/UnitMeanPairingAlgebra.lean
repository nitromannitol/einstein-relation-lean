import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Auxiliary weak-limit and time-testing estimates; source `paper/main.tex:755,808–848`. -/

open MeasureTheory
namespace EinsteinRelation.Correctors

theorem integral_pairing_of_unit_mean_subtraction (U ρ η : ℝ → ℝ)
    (hη : MeasureTheory.Integrable (fun t => U t * η t))
    (hρ : MeasureTheory.Integrable (fun t => U t * ρ t))
    (hz : (∫ t : ℝ, U t * (η t - (∫ s : ℝ, η s) * ρ t)) = 0) :
    (∫ t : ℝ, U t * η t) = (∫ t : ℝ, U t * ρ t) * (∫ t : ℝ, η t) := by
  set C := (∫ s : ℝ, η s) with hC
  have h_int_sub : MeasureTheory.Integrable (fun t : ℝ => U t * (η t - C * ρ t)) := by
    have : (fun t : ℝ => U t * (η t - C * ρ t)) = (fun t => U t * η t) - (fun t => C * (U t * ρ t)) := by
      ext t
      dsimp
      ring
    rw [this]
    exact hη.sub (hρ.const_mul C)
  have h_eq : (∫ t : ℝ, U t * (η t - C * ρ t)) = (∫ t : ℝ, U t * η t) - C * (∫ t : ℝ, U t * ρ t) := by
    calc
      (∫ t : ℝ, U t * (η t - C * ρ t)) = (∫ t : ℝ, (U t * η t) - C * (U t * ρ t)) := by
        refine integral_congr_ae ?_
        filter_upwards [] with t
        ring_nf
      _ = (∫ t : ℝ, U t * η t) - (∫ t : ℝ, C * (U t * ρ t)) := integral_sub hη (hρ.const_mul C)
      _ = (∫ t : ℝ, U t * η t) - C * (∫ t : ℝ, U t * ρ t) := by rw [integral_const_mul C]
  have hz' : (∫ t : ℝ, U t * η t) - C * (∫ t : ℝ, U t * ρ t) = 0 := by
    linarith [h_eq, hz]
  have hgoal : (∫ t : ℝ, U t * η t) = C * (∫ t : ℝ, U t * ρ t) := by
    linarith
  rw [hC, mul_comm]
  exact hgoal

end EinsteinRelation.Correctors
