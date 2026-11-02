import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace EinsteinFull.Blueprint

/-- Node `l:forced-flux#parameters`, `paper/main.tex:827–831`.
The mesoscopic and force-window exponents are fixed from the dimension and
sublinearity exponent, before the environment, force, moment order or time. -/
def node_l_u3A_forced_u2D_flux_u23_parametersStmt : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ κ : ℝ, 0 < κ → κ < 1 / 2 →
    ∃ η η₀ : ℝ,
      η = κ / (16 * ((d : ℝ) + 2)) ∧ η₀ = η / 4 ∧
      0 < η₀ ∧ η₀ < η ∧ η < 1 / 2 ∧
      ∀ t : ℝ, 1 ≤ t →
        let r := t ^ (1 / 2 + η)
        Real.sqrt t ≤ r ∧
        ∀ ζ : ℂ, ‖ζ‖ * Real.sqrt t ≤ t ^ η₀ →
          ‖ζ‖ ^ 2 * t ≤ t ^ (2 * η₀)

end EinsteinFull.Blueprint
