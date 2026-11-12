import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! CutoffHolderPowerIdentity: auxiliary analytic estimates. Source: `paper/main.tex:832–840`. -/
open Filter Topology
namespace EinsteinRelation.Correctors

theorem cutoff_holder_rpow_identity {χ v : ℝ} (hχ : 0 ≤ χ)
    (n : ℕ) (hn : 2 ≤ n) : χ^(2*n-2) * v^2 = (χ^(2*n) * v^2)^(1-(n:ℝ)⁻¹) *
      (v^2)^((n:ℝ)⁻¹) := by
  have hn_real_pos : 0 < (n : ℝ) := by
    have h1 : 1 ≤ n := by omega
    exact_mod_cast h1
  have hn_real_ne_zero : (n : ℝ) ≠ 0 := by linarith
  have hn_real_ge_2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h2n_sub_2_pos : 0 < 2*(n:ℝ) - 2 := by nlinarith
  have h2n_pos : 0 < 2*(n:ℝ) := by nlinarith
  have h_exp1_pos : 0 < 1 - ((n:ℝ)⁻¹) := by
    have hinv_le_half : (n:ℝ)⁻¹ ≤ 1/2 := by
      have h := (one_div_le_one_div hn_real_pos (by norm_num : 0 < (2:ℝ))).mpr hn_real_ge_2
      simpa [one_div] using h
    nlinarith
  have h_exp1_ne_zero : 1 - ((n:ℝ)⁻¹) ≠ 0 := by linarith
  have h_inv_pos : 0 < (n:ℝ)⁻¹ := inv_pos.mpr hn_real_pos
  have h_inv_ne_zero : (n:ℝ)⁻¹ ≠ 0 := by linarith
  have hv2_rpow_nonneg : 0 ≤ v^(2:ℝ) := by
    simpa [Real.rpow_natCast] using pow_two_nonneg v
  have h_rpow_goal : χ^(2*(n:ℝ)-2) * v^(2:ℝ) =
      (χ^(2*(n:ℝ)) * v^(2:ℝ))^(1-(n:ℝ)⁻¹) * (v^(2:ℝ))^((n:ℝ)⁻¹) := by
    by_cases hv2_zero : v^(2:ℝ) = 0
    · rw [hv2_zero]
      simp [h_exp1_pos.ne.symm, h_inv_pos.ne.symm]
    · have hv2_pos : 0 < v^(2:ℝ) :=
        lt_of_le_of_ne hv2_rpow_nonneg (Ne.symm hv2_zero)
      by_cases hχ_zero : χ = 0
      · subst χ
        simp [h2n_sub_2_pos.ne.symm, h2n_pos.ne.symm, h_exp1_pos.ne.symm]
      · have hχ_pos : 0 < χ := lt_of_le_of_ne hχ (Ne.symm hχ_zero)
        have h_exp_eq : 2*(n:ℝ)-2 = (2*(n:ℝ)) * (1 - ((n:ℝ)⁻¹)) := by
          field_simp [hn_real_ne_zero]
        calc
          χ^(2*(n:ℝ)-2) * v^(2:ℝ)
              = χ^((2*(n:ℝ)) * (1 - ((n:ℝ)⁻¹))) * v^(2:ℝ) := by rw [h_exp_eq]
          _ = (χ^(2*(n:ℝ)))^(1 - ((n:ℝ)⁻¹)) * v^(2:ℝ) := by
                rw [Real.rpow_mul hχ]
          _ = (χ^(2*(n:ℝ)))^(1 - ((n:ℝ)⁻¹)) *
              (v^(2:ℝ))^(((1 - ((n:ℝ)⁻¹)) + ((n:ℝ)⁻¹))) := by
                rw [show ((1 - ((n:ℝ)⁻¹)) + ((n:ℝ)⁻¹)) = (1 : ℝ) by ring,
                  Real.rpow_one]
          _ = (χ^(2*(n:ℝ)))^(1 - ((n:ℝ)⁻¹)) *
              ((v^(2:ℝ))^(1 - ((n:ℝ)⁻¹)) * (v^(2:ℝ))^((n:ℝ)⁻¹)) := by
                rw [Real.rpow_add hv2_pos]
          _ = ((χ^(2*(n:ℝ)))^(1 - ((n:ℝ)⁻¹)) * (v^(2:ℝ))^(1 - ((n:ℝ)⁻¹))) *
              (v^(2:ℝ))^((n:ℝ)⁻¹) := by ring
          _ = ((χ^(2*(n:ℝ)) * v^(2:ℝ))^(1 - ((n:ℝ)⁻¹))) *
              (v^(2:ℝ))^((n:ℝ)⁻¹) := by
                rw [← Real.mul_rpow (Real.rpow_nonneg hχ _) hv2_rpow_nonneg]
  have h2n_ge_2 : 2 ≤ 2*n := by omega
  -- Rewrite the goal to match h_rpow_goal
  rw [show χ^(2*n-2) = χ^(2*(n:ℝ)-2) by
    rw [← Real.rpow_natCast]
    congr
    simp [Nat.cast_sub h2n_ge_2, Nat.cast_mul, Nat.cast_ofNat]]
  rw [← Real.rpow_natCast v 2]
  rw [show χ^(2*n) = χ^(2*(n:ℝ)) by
    rw [← Real.rpow_natCast]
    congr
    simp]
  exact h_rpow_goal

end EinsteinRelation.Correctors
