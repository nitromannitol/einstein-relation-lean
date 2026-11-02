import EinsteinFull.Calculus.C5TubeSymmetricPowerFatou
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

open MeasureTheory Filter
open PDE.Parabolic.LocalMax
open scoped ENNReal

namespace EinsteinFull.Calculus

noncomputable section

/-- A uniform bound on both signed truncations bounds the full absolute moment. -/
theorem c5_signed_moment_bound_of_symmetric_truncations
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (u : X → ℝ)
    (hu : AEStronglyMeasurable u μ) (p ε : ℝ) (hp : 2 ≤ p) (hε : 0 < ε)
    (B : ℝ≥0∞)
    (hbound : ∀ n : ℕ, (∫⁻ x, ENNReal.ofReal
      (powF p ε (n : ℝ) (u x) + powF p ε (n : ℝ) (-u x)) ∂μ) ≤ B) :
    (∫⁻ x, ENNReal.ofReal (Real.rpow |u x| p) ∂μ) ≤ B := by
  apply (c5_symmetric_truncated_power_fatou μ u hu p ε hp hε).trans
  exact liminf_le_of_frequently_le' (Filter.Eventually.frequently (Filter.Eventually.of_forall hbound))

/-- A uniform signed truncation estimate transfers a moment bound between measures. -/
theorem c5_signed_moment_gain_of_symmetric_truncations
    {X : Type*} [MeasurableSpace X] (μ ν : Measure X) (u : X → ℝ)
    (hu : AEStronglyMeasurable u μ) (p q : ℝ) (hp : 2 ≤ p)
    (C : ℝ≥0∞)
    (hbound : ∃ ε : ℝ, 0 < ε ∧ ∀ n : ℕ,
      (∫⁻ x, ENNReal.ofReal
        (powF p ε (n : ℝ) (u x) + powF p ε (n : ℝ) (-u x)) ∂μ) ≤
      C * (∫⁻ x, ENNReal.ofReal (Real.rpow |u x| q) ∂ν)) :
    (∫⁻ x, ENNReal.ofReal (Real.rpow |u x| p) ∂μ) ≤
      C * (∫⁻ x, ENNReal.ofReal (Real.rpow |u x| q) ∂ν) := by
  obtain ⟨ε, hε, h⟩ := hbound
  exact c5_signed_moment_bound_of_symmetric_truncations μ u hu p ε hp hε _ h

/-- A finite signed truncation bound gives membership in the corresponding Lp space. -/
theorem c5_memLp_of_symmetric_truncations
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (u : X → ℝ)
    (hu : AEStronglyMeasurable u μ) (p ε : ℝ) (hp : 2 ≤ p) (hε : 0 < ε)
    (B : ℝ≥0∞) (hB : B ≠ ⊤)
    (hbound : ∀ n : ℕ, (∫⁻ x, ENNReal.ofReal
      (powF p ε (n : ℝ) (u x) + powF p ε (n : ℝ) (-u x)) ∂μ) ≤ B) :
    MemLp u (ENNReal.ofReal p) μ := by
  have hp0 : 0 < p := by linarith
  have hmoment := lt_of_le_of_lt
    (c5_signed_moment_bound_of_symmetric_truncations μ u hu p ε hp hε B hbound)
    (lt_top_iff_ne_top.mpr hB)
  refine (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (ne_of_gt (ENNReal.ofReal_pos.mpr hp0)) ENNReal.ofReal_ne_top hu).2 ?_
  simpa [ENNReal.toReal_ofReal hp0.le, ← ENNReal.ofReal_rpow_of_nonneg
    (abs_nonneg _) hp0.le, Real.enorm_eq_ofReal_abs] using hmoment

end
end EinsteinFull.Calculus
