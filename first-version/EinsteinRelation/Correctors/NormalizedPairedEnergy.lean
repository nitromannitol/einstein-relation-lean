import EinsteinRelation.Correctors.PairedEnergyNormalization
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Normalization of the paired power-cutoff energy

Source: `paper/main.tex:826–843`. The source energy estimate is invariant
under division by spatial volume. This cancellation retains a single
power-cutoff exponent and the same energy constant.
-/

open MeasureTheory
namespace EinsteinRelation.Correctors

/-- Division by the spatial volume preserves the power-energy inequality.
Source: `paper/main.tex:826–843`. -/
theorem normalized_power_energy_le {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (n : ℕ) (hn : 0 < n) {s K : ℝ} (hs : 0 < s)
    (A E : X → ℝ) (hA : ∀ t, 0 ≤ A t)
    (henergy : (∫ t, E t ∂ν) ≤ (K * ∫ t, (A t)^((n : ℝ)⁻¹) ∂ν)^n) :
    (∫ t, s⁻¹ * E t ∂ν) ≤ (K * ∫ t, (s⁻¹ * A t)^((n : ℝ)⁻¹) ∂ν)^n := by
  have hid : (∫ t, (s⁻¹ * A t)^((n : ℝ)⁻¹) ∂ν) =
      (s⁻¹)^((n : ℝ)⁻¹) * ∫ t, (A t)^((n : ℝ)⁻¹) ∂ν := by
    simp only [Real.mul_rpow (inv_nonneg.mpr hs.le) (hA _), integral_const_mul]
  rw [integral_const_mul, hid]
  calc
    s⁻¹ * (∫ t, E t ∂ν) ≤ s⁻¹ * (K * ∫ t, (A t)^((n : ℝ)⁻¹) ∂ν)^n :=
      mul_le_mul_of_nonneg_left henergy (inv_nonneg.mpr hs.le)
    _ = _ := by rw [paired_energy_normalization n hn hs]; congr 1; ring

/-- The literal unnormalized spatial energy bound yields its normalized
set-average version. Source: `paper/main.tex:826–843`. -/
theorem setAverage_power_energy_le {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (ν : Measure X) (μ : Measure Y) (U : Set Y) (n : ℕ) (hn : 0 < n)
    (hU : 0 < μ.real U) (K : ℝ) (u e : X → Y → ℝ)
    (henergy : (∫ t, ∫ x in U, e t x ∂μ ∂ν) ≤
      (K * ∫ t, (∫ x in U, (u t x)^2 ∂μ)^((n : ℝ)⁻¹) ∂ν)^n) :
    (∫ t, ⨍ x in U, e t x ∂μ ∂ν) ≤
      (K * ∫ t, (⨍ x in U, (u t x)^2 ∂μ)^((n : ℝ)⁻¹) ∂ν)^n := by
  simpa only [setAverage_eq, smul_eq_mul] using normalized_power_energy_le ν n hn hU
    (fun t => ∫ x in U, (u t x)^2 ∂μ) (fun t => ∫ x in U, e t x ∂μ)
    (fun t => integral_nonneg fun x => sq_nonneg _) henergy

end EinsteinRelation.Correctors
