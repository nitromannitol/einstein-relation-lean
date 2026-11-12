import EinsteinRelation.Correctors.AKMPlanarOscillationMoments

/-! Source: `paper/main.tex:724-731`. Admissible scales in the repaired planar proof. -/
namespace EinsteinRelation.Correctors
open External.AKM

theorem four_eight_scale_geometry (r R q : ℝ) (hr : 1 ≤ r) (hR : 1 ≤ R)
    (hq0 : 0 ≤ q) (hq : q ≤ 2 * R + 4) :
    4 < (8 * R) / Real.sqrt 2 ∧
    Real.sqrt (Real.log (2 + (8 * R + q / r) / 4)) ≤
      2 * Real.sqrt (Real.log (2 + R)) := by
  have h_sqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h_sqrt2_lt_2 : Real.sqrt 2 < 2 := by
    have hsq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hsq_lt : (Real.sqrt 2) ^ 2 < 2 ^ 2 := by
      calc
        (Real.sqrt 2) ^ 2 = 2 := hsq
        _ < 4 := by norm_num
        _ = 2 ^ 2 := by norm_num
    nlinarith
  have h_left : 4 < (8 * R) / Real.sqrt 2 := by
    field_simp [ne_of_gt h_sqrt2_pos]
    nlinarith
  have h_right : Real.sqrt (Real.log (2 + (8 * R + q / r) / 4)) ≤
      2 * Real.sqrt (Real.log (2 + R)) := by
    have h_nonneg_log_right : 0 ≤ Real.log (2 + R) := by
      apply Real.log_nonneg
      nlinarith
    have h_log_main : Real.log (2 + (8 * R + q / r) / 4) ≤ 4 * Real.log (2 + R) := by
      have h_arg_pos : 0 < 2 + (8 * R + q / r) / 4 := by
        have h8R : 0 ≤ 8 * R := by nlinarith
        have hqdivr : 0 ≤ q / r := div_nonneg hq0 (by nlinarith)
        nlinarith
      have h_ineq : 2 + (8 * R + q / r) / 4 ≤ (2 + R) ^ 4 := by
        have hqdivr_le_q : q / r ≤ q :=
          div_le_self hq0 hr
        have h_bound : 2 + (8 * R + q / r) / 4 ≤ (5 * R + 6) / 2 := by
          nlinarith
        have h_final : (5 * R + 6) / 2 ≤ (2 + R) ^ 4 := by
          have hRpos : 0 ≤ R := by nlinarith
          have h_sq_bound : (5 * R + 6) / 2 ≤ (2 + R) ^ 2 := by
            have : (2 + R) ^ 2 = R ^ 2 + 4 * R + 4 := by ring
            rw [this]
            nlinarith
          have h_pow_bound : (2 + R) ^ 2 ≤ (2 + R) ^ 4 := by
            have h_base_sq_ge_one : 1 ≤ (2 + R) ^ 2 := by
              have h_base_ge_one : 1 ≤ 2 + R := by nlinarith
              nlinarith
            calc
              (2 + R) ^ 2 = (2 + R) ^ 2 * 1 := by ring
              _ ≤ (2 + R) ^ 2 * (2 + R) ^ 2 := by nlinarith
              _ = (2 + R) ^ 4 := by ring
          nlinarith
        nlinarith
      calc
        Real.log (2 + (8 * R + q / r) / 4) ≤ Real.log ((2 + R) ^ 4) :=
          Real.log_le_log h_arg_pos h_ineq
        _ = 4 * Real.log (2 + R) := by rw [Real.log_pow, Nat.cast_ofNat]
    calc
      Real.sqrt (Real.log (2 + (8 * R + q / r) / 4)) ≤
          Real.sqrt (4 * Real.log (2 + R)) := Real.sqrt_le_sqrt h_log_main
      _ = Real.sqrt ((2 : ℝ) ^ 2 * Real.log (2 + R)) := by norm_num
      _ = Real.sqrt ((2 : ℝ) ^ 2) * Real.sqrt (Real.log (2 + R)) := by
        rw [Real.sqrt_mul (by norm_num : 0 ≤ (2 : ℝ) ^ 2)]
      _ = 2 * Real.sqrt (Real.log (2 + R)) := by
        rw [Real.sqrt_sq (by norm_num : 0 ≤ (2 : ℝ))]
  exact And.intro h_left h_right
end EinsteinRelation.Correctors
