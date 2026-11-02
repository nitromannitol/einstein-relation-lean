import EinsteinFull.Frozen.ReducedClockRate
import EinsteinFull.Frozen.SignedPhysicalFamily
import EinsteinFull.Frozen.HomogenizedCoefficient

open MeasureTheory Filter
open scoped Topology NNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Graph node `eq.time-change-identities#forced-lln`, `paper/main.tex:227`.
Each fixed signed nonzero force has deterministic velocities for the actual
physical and reduced laws; the almost-sure events may depend on force. -/
def node_eq_u2E_time_u2D_change_u2D_identities_u23_forced_u2D_llnStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ)
    (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ), lam ≠ 0 → ∀ X Y : QuenchedPathLaws d,
    (∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (physicalGenerator (⟨0, by omega⟩ : Fin d) ω lam)
        0 (X (0, ω))) →
    (∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator (⟨0, by omega⟩ : Fin d) ω lam)
        0 (Y (0, ω))) →
    ∃ vX vY : Vec d,
      HasQuenchedVelocity Q.measure (originLaw X) vX ∧
      HasQuenchedVelocity Q.measure (originLaw Y) vY ∧
      0 < lam * vX ⟨0, by omega⟩ ∧ 0 < lam * vY ⟨0, by omega⟩

end EinsteinFull.Blueprint
