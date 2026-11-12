import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace EinsteinRelation.Correctors

/-- Volume cancels from the power-cutoff energy estimate,
paper/main.tex:826–843. -/
theorem paired_energy_normalization (n : ℕ) (hn : 0 < n)
    {s K J : ℝ} (hs : 0 < s) :
    s⁻¹ * (K * J)^n = (K * (s⁻¹)^((n : ℝ)⁻¹) * J)^n := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hs_nonneg : 0 ≤ s⁻¹ := le_of_lt (inv_pos.mpr hs)
  have h_key : s⁻¹ = ((s⁻¹)^((n : ℝ)⁻¹))^n := by
    calc
      s⁻¹ = (s⁻¹)^(1 : ℝ) := by rw [Real.rpow_one]
      _ = (s⁻¹)^(((n : ℝ)⁻¹) * (n : ℝ)) := by rw [inv_mul_cancel₀ hn']
      _ = ((s⁻¹)^((n : ℝ)⁻¹))^n := by rw [Real.rpow_mul_natCast hs_nonneg ((n : ℝ)⁻¹) n]
  calc
    s⁻¹ * (K * J)^n = ((s⁻¹)^((n : ℝ)⁻¹))^n * (K * J)^n := by
      nth_rw 1 [h_key]
    _ = (((s⁻¹)^((n : ℝ)⁻¹)) * (K * J))^n := by rw [← mul_pow]
    _ = ((s⁻¹)^((n : ℝ)⁻¹) * K * J)^n := by simp [mul_assoc]
    _ = (K * (s⁻¹)^((n : ℝ)⁻¹) * J)^n := by simp [mul_comm, mul_left_comm]

end EinsteinRelation.Correctors
