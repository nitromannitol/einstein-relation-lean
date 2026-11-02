import EinsteinFull.Blueprint.Foundation.node_eq_u2E_reduced_u2D_bounds
import EinsteinFull.Frozen.SmoothEnvironment

open MeasureTheory

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Graph node `eq.reduced-bounds#derivatives`, `paper/main.tex:222`.
One deterministic sequence, chosen before the law, bounds every derivative
order of the actual reduced fields on a single almost-sure event. The norms
are the explicit Euclidean multilinear/operator bounds of Assumption 1.2. -/
def node_eq_u2E_reduced_u2D_bounds_u23_derivativesStmt : Prop :=
  ∀ (d : ℕ) (D : StructuralData d), ∃ M : ℕ → ℝ,
    (∀ k : ℕ, 1 ≤ k → 0 < M k) ∧
    ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      HasSmoothBounds D Q → ∀ᵐ ω ∂reducedLaw Q, IsSmoothWithBounds M ω

end EinsteinFull.Blueprint
