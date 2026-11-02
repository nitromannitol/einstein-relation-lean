import EinsteinFull.Frozen.ReducedClockRate
import EinsteinFull.Frozen.SignedPhysicalFamily
import EinsteinFull.Frozen.HomogenizedCoefficient
import EinsteinFull.Frozen.SmoothWithBounds

open MeasureTheory Filter
open scoped Topology NNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Smooth-scope version `V2` of `node_eq_u2E_time_u2D_change_u2D_identities_u23_forced_u2D_llnStmt`
(`eq.time-change-identities#forced-lln`, `paper/main.tex:227`), in the `Λ₀`-first form: the law keeps its
type `EnvironmentLaw d Λ₀ r₀`, and Assumption 1.2 is stated as the derivative-bound sequence `b` with
`IsSmoothWithBounds b ω` almost surely (this is `HasSmoothBounds D Q` for `D = ⟨Λ₀, r₀, b, ..⟩`). The
structural data are constrained as in `StructuralData` (`1 ≤ Λ₀`, `1 ≤ r₀`, `0 < b k` for `k ≥ 1`);
the conclusion is verbatim. -/
def node_eq_u2E_time_u2D_change_u2D_identities_u23_forced_u2D_llnStmtV2 : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (b : ℕ → ℝ)
    (Q : EnvironmentLaw d Λ₀ r₀),
    1 ≤ Λ₀ → 1 ≤ r₀ → (∀ k : ℕ, 1 ≤ k → 0 < b k) →
    (∀ᵐ ω ∂Q.measure, IsSmoothWithBounds b ω) →
    ∀ (lam : ℝ), lam ≠ 0 → ∀ X Y : QuenchedPathLaws d,
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
