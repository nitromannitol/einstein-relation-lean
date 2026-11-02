import EinsteinFull.Frozen.ReducedClockRate
import EinsteinFull.Frozen.SignedPhysicalFamily
import EinsteinFull.Frozen.HomogenizedCoefficient

open MeasureTheory Filter
open scoped Topology NNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Graph node `eq.time-change-identities#unforced-clock`, `paper/main.tex:232`.
The unforced clock limit is the expectation of the actual joint clock.
The physical invariance-principle covariance retains the anisotropic matrix. -/
def node_eq_u2E_time_u2D_change_u2D_identities_u23_unforced_u2D_clockStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ)
    (Q : EnvironmentLaw d Λ₀ r₀),
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
