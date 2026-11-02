import EinsteinFull.Blueprint.G2.node_l_u3A_forced_u2D_flux_u23_parameters
import EinsteinFull.Blueprint.G3.node_e_u3A_sublinear_u2D_pair
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace EinsteinFull.Blueprint

/-- The parameter choice in `paper/main.tex:827–831` and its force-window
consequence. The graph dependency supplies the structural sublinearity exponent;
the algebra holds for every exponent in its stated range, so this mandatory
dependency binder is unused. -/
@[nolint unusedArguments]
theorem node_l_u3A_forced_u2D_flux_u23_parameters_of_deps
    (_hSublinear : node_e_u3A_sublinear_u2D_pairStmt) :
    node_l_u3A_forced_u2D_flux_u23_parametersStmt := by
  intro d hd κ hκ hκhalf
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hden : (0 : ℝ) < 16 * ((d : ℝ) + 2) := by linarith
  let η := κ / (16 * ((d : ℝ) + 2))
  have hη : 0 < η := div_pos hκ hden
  have hηhalf : η < 1 / 2 := by
    apply (div_lt_iff₀ hden).2
    linarith
  refine ⟨η, η / 4, rfl, rfl, div_pos hη (by norm_num), ?_, hηhalf, ?_⟩
  · linarith
  · intro t ht
    have ht0 : 0 ≤ t := le_trans zero_le_one ht
    constructor
    · rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le ht (by linarith)
    · intro ζ hζ
      have hsquare := mul_self_le_mul_self (mul_nonneg (norm_nonneg ζ)
        (Real.sqrt_nonneg t)) hζ
      calc
        ‖ζ‖ ^ 2 * t = (‖ζ‖ * Real.sqrt t) * (‖ζ‖ * Real.sqrt t) := by
          rw [mul_mul_mul_comm, Real.mul_self_sqrt ht0, pow_two]
        _ ≤ (t ^ (η / 4)) * (t ^ (η / 4)) := hsquare
        _ = t ^ (2 * (η / 4)) := by
          rw [two_mul, Real.rpow_add (lt_of_lt_of_le zero_lt_one ht)]

end EinsteinFull.Blueprint
