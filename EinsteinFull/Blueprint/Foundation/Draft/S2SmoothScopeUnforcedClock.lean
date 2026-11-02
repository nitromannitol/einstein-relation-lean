import EinsteinFull.Frozen.ReducedClockRate
import EinsteinFull.Frozen.SignedPhysicalFamily
import EinsteinFull.Frozen.HomogenizedCoefficient
import EinsteinFull.Frozen.SmoothWithBounds

open MeasureTheory Filter
open scoped Topology NNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- DRAFT smooth-scope V2 of `node_eq_u2E_time_u2D_change_u2D_identities_u23_unforced_u2D_clockStmt`, paper/main.tex:232.
Only the law's Assumption 1.2 smoothness block is added; all following hypotheses
and conclusions are byte-identical to V1. Signed forces, full anisotropic matrix,
a.e. qualifiers, actual laws and inverse clock remain literal. The full time-change
statement retains the Lambda0-first bound, before dimension and derivative data.
Not elaborated or reviewed yet; not imported by production; no V1/root replacement. -/
def node_eq_u2E_time_u2D_change_u2D_identities_u23_unforced_u2D_clockStmtV2 : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (b : ℕ → ℝ)
    (Q : EnvironmentLaw d Λ₀ r₀),
    1 ≤ Λ₀ → 1 ≤ r₀ → (∀ k : ℕ, 1 ≤ k → 0 < b k) →
    (∀ᵐ ω ∂Q.measure, IsSmoothWithBounds b ω) →
    ∀ X Y : QuenchedPathLaws d,
    (∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (physicalGenerator (⟨0, by omega⟩ : Fin d) ω 0)
        0 (X (0, ω))) →
    (∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator (⟨0, by omega⟩ : Fin d) ω 0)
        0 (Y (0, ω))) →
    (∀ᵐ ω ∂Q.measure, ∃ hω : IsRegular Λ₀ ω,
      X (0, ω) = (Y (0, ω)).map
        (fun γ => Clock.InverseMeaningV3.inverseClockPath ω γ Λ₀ hω)) →
    HasReducedClockRate Q Y (∫ ω, ω.2 0 ∂reducedLaw Q) ∧
    HasDiffusivity Q.measure (originLaw X)
      ((∫ ω, ω.2 0 ∂reducedLaw Q)⁻¹ • homogenizedCoefficient Q)


end EinsteinFull.Blueprint
