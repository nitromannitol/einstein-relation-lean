import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace EinsteinRelation.Correctors

/-- Weighted energy to integrated gradient size, paper/main.tex:841–849. -/
theorem paired_energy_sqrt_bound {F E C R T J : ℝ} {n : ℕ}
    (hE : 0 ≤ E) (hC : 0 ≤ C) (hR : 0 < R) (hT : 0 ≤ T) (hJ : 0 ≤ J)
    (henergy : E ≤ (C / R^2 * J)^n) (hcs : F^2 ≤ T * E) :
    F ≤ Real.sqrt T * (Real.sqrt C)^n * R^(-(n : ℝ)) * J^((n : ℝ)/2) := by
  -- If F ≤ 0, the inequality holds trivially since RHS ≥ 0
  by_cases hF : F ≤ 0
  · have hRHS_nonneg : 0 ≤ Real.sqrt T * (Real.sqrt C)^n * R^(-(n : ℝ)) * J^((n : ℝ)/2) := by
      positivity
    linarith
  · have hF_nonneg : 0 ≤ F := by linarith
    -- The base C/R^2*J is non-negative
    have h_base_nonneg : 0 ≤ C / R^2 * J := by
      have h_div : 0 ≤ C / R^2 := div_nonneg hC (by positivity)
      exact mul_nonneg h_div hJ
    -- Combine the inequalities: F^2 ≤ T * ((C/R^2*J)^n)
    have h1 : F^2 ≤ T * ((C / R^2 * J)^n) := by
      have hTE : T * E ≤ T * ((C / R^2 * J)^n) :=
        mul_le_mul (le_refl T) henergy hE hT
      linarith
    -- Take square root of both sides
    have h2 : Real.sqrt (F^2) ≤ Real.sqrt (T * ((C / R^2 * J)^n)) :=
      Real.sqrt_le_sqrt h1
    -- Simplify RHS: sqrt(T * X) = sqrt(T) * sqrt(X) since T ≥ 0
    have h4 : Real.sqrt (T * ((C / R^2 * J)^n)) = Real.sqrt T * Real.sqrt ((C / R^2 * J)^n) :=
      Real.sqrt_mul hT _
    -- Simplify sqrt((C/R^2*J)^n) = (sqrt(C/R^2*J))^n
    have h5 : Real.sqrt ((C / R^2 * J)^n) = (Real.sqrt (C / R^2 * J))^n := by
      let x := C / R^2 * J
      have hx_nonneg : 0 ≤ x := h_base_nonneg
      calc
        Real.sqrt (x ^ n) = (x ^ n) ^ (1 / (2 : ℝ)) := by rw [Real.sqrt_eq_rpow]
        _ = (x ^ (n : ℝ)) ^ (1 / (2 : ℝ)) := by rw [Real.rpow_natCast]
        _ = x ^ ((n : ℝ) * (1 / (2 : ℝ))) := by rw [Real.rpow_mul hx_nonneg]
        _ = x ^ ((n : ℝ) / 2) := by congr 1; ring
        _ = (Real.sqrt x) ^ (n : ℝ) := by rw [Real.rpow_div_two_eq_sqrt (n : ℝ) hx_nonneg]
        _ = (Real.sqrt x) ^ n := by rw [Real.rpow_natCast]
    -- Now simplify sqrt(C/R^2*J)
    have h6 : Real.sqrt (C / R^2 * J) = (Real.sqrt C / R) * Real.sqrt J := by
      calc
        Real.sqrt (C / R^2 * J) = Real.sqrt (C / R^2) * Real.sqrt J :=
          Real.sqrt_mul (div_nonneg hC (by positivity)) _
        _ = (Real.sqrt C / Real.sqrt (R^2)) * Real.sqrt J := by rw [Real.sqrt_div hC _]
        _ = (Real.sqrt C / R) * Real.sqrt J := by rw [Real.sqrt_sq (by positivity : 0 ≤ R)]
    -- Combine h5 and h6
    have h7 : Real.sqrt ((C / R^2 * J)^n) = ((Real.sqrt C / R) * Real.sqrt J)^n := by
      rw [h5, h6]
    -- Now we need to relate the two RHS expressions
    -- Key identity: ((√C / R) * √J)^n = (√C)^n * R^(-(n : ℝ)) * J^((n : ℝ)/2)
    have h8 : ((Real.sqrt C / R) * Real.sqrt J) ^ n =
             (Real.sqrt C)^n * R^(-(n : ℝ)) * J^((n : ℝ)/2) := by
      calc
        ((Real.sqrt C / R) * Real.sqrt J) ^ n =
            (Real.sqrt C / R)^n * (Real.sqrt J)^n := by ring
        _ = ((Real.sqrt C)^n / R^n) * (Real.sqrt J)^n := by ring
        _ = (Real.sqrt C)^n * (R^n)⁻¹ * (Real.sqrt J)^n := by ring
        _ = (Real.sqrt C)^n * ((R ^ (n : ℝ))⁻¹) * (Real.sqrt J)^n := by rw [Real.rpow_natCast]
        _ = (Real.sqrt C)^n * R^(-(n : ℝ)) * (Real.sqrt J)^n := by
          rw [Real.rpow_neg (by positivity : 0 ≤ R)]
        _ = (Real.sqrt C)^n * R^(-(n : ℝ)) * ((Real.sqrt J) ^ (n : ℝ)) := by rw [Real.rpow_natCast]
        _ = (Real.sqrt C)^n * R^(-(n : ℝ)) * (J ^ ((n : ℝ)/2)) := by
          rw [Real.rpow_div_two_eq_sqrt (n : ℝ) hJ]
    -- Now combine everything
    calc
      F = Real.sqrt (F^2) := by rw [Real.sqrt_sq hF_nonneg]
      _ ≤ Real.sqrt (T * ((C / R^2 * J)^n)) := h2
      _ = Real.sqrt T * Real.sqrt ((C / R^2 * J)^n) := h4
      _ = Real.sqrt T * (((Real.sqrt C / R) * Real.sqrt J) ^ n) := by rw [h7]
      _ = Real.sqrt T * ((Real.sqrt C)^n * R^(-(n : ℝ)) * J^((n : ℝ)/2)) := by rw [h8]
      _ = Real.sqrt T * (Real.sqrt C)^n * R^(-(n : ℝ)) * J^((n : ℝ)/2) := by ring

end EinsteinRelation.Correctors
