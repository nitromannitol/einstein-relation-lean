import EinsteinFull.Blueprint.G3.node_e_u3A_parameters
import EinsteinFull.Blueprint.Foundation.node_eq_u2E_reduced_u2D_bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace EinsteinFull.Blueprint

/-- Structural localization parameters for graph node `e:parameters`,
`paper/main.tex:898–905`, chosen before the law and scales. -/
theorem node_e_u3A_parameters_of_deps
    (hBounds : node_eq_u2E_reduced_u2D_boundsStmt) : node_e_u3A_parametersStmt := by
  intro d hd _D
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨Λ, _, _, hΛ, _⟩ := hBounds _D.ellipticity _D.one_le_ellipticity
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  let ε : ℝ := 1 / (8 * Λ)
  have hεpos : 0 < ε := one_div_pos.mpr (mul_pos (by norm_num) hΛpos)
  have hεle : ε ≤ 1 / 8 := by
    apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 8) hΛpos)).2
    linarith
  let γ : ℝ := 5 * d / 8 + ε
  have hγ : 0 < 2 * γ := by dsimp [γ]; linarith
  have hη : max ((d : ℝ) / (2 * γ)) (1 / 2) < (4 / 5 : ℝ) := by
    apply max_lt
    · apply (div_lt_iff₀ hγ).2
      dsimp [γ]
      linarith
    · norm_num
  obtain ⟨η, hηlo, hηhi⟩ := exists_between hη
  have hηlower : (d : ℝ) / (2 * γ) < η :=
    lt_of_le_of_lt (le_max_left _ _) hηlo
  have hηhalf : (1 / 2 : ℝ) < η :=
    lt_of_le_of_lt (le_max_right _ _) hηlo
  have hβ : η * (1 + (1 / 4 : ℝ)) < 1 := by linarith
  obtain ⟨β, hβlo, hβhi⟩ := exists_between hβ
  obtain ⟨η₂, hη₂lo, hη₂hi⟩ := exists_between hηhi
  refine ⟨4 / 3, 1 / 4, γ, η, β, η₂, ?_⟩
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_, ?_,
    hηlower, ?_, hηhalf, hβlo, hβhi, hη₂lo, ?_⟩
  · dsimp [γ]; linarith
  · dsimp [γ]; linarith
  · dsimp [γ]; linarith
  · convert hηhi using 1; norm_num
  · convert hη₂hi using 1; norm_num

end EinsteinFull.Blueprint
