import EinsteinFull.Frozen.StructuralData
import Mathlib.Data.Real.Basic

namespace EinsteinFull.Blueprint

/-- Graph node `e:parameters`, `paper/main.tex:898–905`.
All localization parameters are chosen before the environment law or scales.
The two separate upper bounds on gamma spell out the displayed minimum. -/
def node_e_u3A_parametersStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (_D : StructuralData d),
    ∃ s δ γ η β η₂ : ℝ,
      1 < s ∧ s < 2 ∧ 0 < δ ∧
      (d : ℝ) / 2 * (1 + δ) < γ ∧
      γ < (d : ℝ) / s ∧ γ < (d : ℝ) / 2 * (1 + δ) + δ ∧
      (d : ℝ) / (2 * γ) < η ∧ η < (1 + δ)⁻¹ ∧
      1 / 2 < η ∧ η * (1 + δ) < β ∧ β < 1 ∧
      η < η₂ ∧ η₂ < (1 + δ)⁻¹

end EinsteinFull.Blueprint
