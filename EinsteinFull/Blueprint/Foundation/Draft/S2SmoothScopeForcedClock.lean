import EinsteinFull.Frozen.ReducedClockRate
import EinsteinFull.Frozen.SignedPhysicalFamily
import EinsteinFull.Frozen.HomogenizedCoefficient
import EinsteinFull.Frozen.SmoothWithBounds

open MeasureTheory Filter
open scoped Topology NNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Smooth-scope version `V2` of `node_eq_u2E_time_u2D_change_u2D_identities_u23_forced_u2D_clockStmt`
(`eq.time-change-identities#forced-clock`, `paper/main.tex:227–231`), `Λ₀`-first: the constant `Λ` is chosen
after `Λ₀` and before `d, r₀, b, Q`, exactly as printed; the only change is the smooth block
`1 ≤ r₀ → (∀ k ≥ 1, 0 < b k) → (∀ᵐ ω, IsSmoothWithBounds b ω) →` after the law, with `b` the derivative-bound
sequence of Assumption 1.2. The conclusion is verbatim. -/
def node_eq_u2E_time_u2D_change_u2D_identities_u23_forced_u2D_clockStmtV2 : Prop :=
  ∀ Λ₀ : ℝ, 1 ≤ Λ₀ → ∃ Λ : ℝ, 1 ≤ Λ ∧
    ∀ (d : ℕ) (hd : 2 ≤ d) (r₀ : ℝ) (b : ℕ → ℝ)
    (Q : EnvironmentLaw d Λ₀ r₀),
    1 ≤ r₀ → (∀ k : ℕ, 1 ≤ k → 0 < b k) →
    (∀ᵐ ω ∂Q.measure, IsSmoothWithBounds b ω) →
    ∀ (lam : ℝ), lam ≠ 0 → ∀ X Y : QuenchedPathLaws d,
    (∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (physicalGenerator (⟨0, by omega⟩ : Fin d) ω lam)
        0 (X (0, ω))) →
    (∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator (⟨0, by omega⟩ : Fin d) ω lam)
        0 (Y (0, ω))) →
    (∀ᵐ ω ∂Q.measure, ∃ hω : IsRegular Λ₀ ω,
      X (0, ω) = (Y (0, ω)).map
        (fun γ => Clock.InverseMeaningV3.inverseClockPath ω γ Λ₀ hω)) →
    ∃ (η : ℝ) (vX vY : Vec d),
      Λ⁻¹ ≤ η ∧ η ≤ Λ ∧ HasReducedClockRate Q Y η ∧
      HasQuenchedVelocity Q.measure (originLaw X) vX ∧
      HasQuenchedVelocity Q.measure (originLaw Y) vY ∧
      0 < lam * vX ⟨0, by omega⟩ ∧ 0 < lam * vY ⟨0, by omega⟩ ∧
      η = vY ⟨0, by omega⟩ / vX ⟨0, by omega⟩ ∧ vX = η⁻¹ • vY

end EinsteinFull.Blueprint
