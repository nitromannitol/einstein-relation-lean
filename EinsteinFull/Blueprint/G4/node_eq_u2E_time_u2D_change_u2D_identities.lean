import EinsteinFull.Frozen.ReducedClockRate
import EinsteinFull.Frozen.SignedPhysicalFamily
import EinsteinFull.Frozen.HomogenizedCoefficient

open MeasureTheory Filter
open scoped Topology NNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Graph node `eq.time-change-identities`, `paper/main.tex:227–232`.
The structural clock bound precedes both path-law families. Fixed-force
velocity identities and the unforced covariance use the same actual clock. -/
def node_eq_u2E_time_u2D_change_u2D_identitiesStmt : Prop :=
  ∀ Λ₀ : ℝ, 1 ≤ Λ₀ → ∃ Λ : ℝ, 1 ≤ Λ ∧
    ∀ (d : ℕ) (hd : 2 ≤ d) (r₀ : ℝ)
    (Q : EnvironmentLaw d Λ₀ r₀),
    ∀ X Y : DiffusionFamily d,
    IsSignedPhysicalFamily (⟨0, by omega⟩ : Fin d) Q X →
    (∀ lam : ℝ, ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator (⟨0, by omega⟩ : Fin d) ω lam)
        0 (Y lam (0, ω))) →
    (∀ lam : ℝ, ∀ᵐ ω ∂Q.measure, ∃ hω : IsRegular Λ₀ ω,
      X lam (0, ω) = (Y lam (0, ω)).map
        (fun γ => Clock.InverseMeaningV3.inverseClockPath ω γ Λ₀ hω)) →
    (∀ lam : ℝ, lam ≠ 0 → ∃ (η : ℝ) (vX vY : Vec d),
      Λ⁻¹ ≤ η ∧ η ≤ Λ ∧ HasReducedClockRate Q (Y lam) η ∧
      HasQuenchedVelocity Q.measure (originLaw (X lam)) vX ∧
      HasQuenchedVelocity Q.measure (originLaw (Y lam)) vY ∧ vX = η⁻¹ • vY) ∧
    HasReducedClockRate Q (Y 0) (∫ ω, ω.2 0 ∂reducedLaw Q) ∧
    HasDiffusivity Q.measure (originLaw (X 0))
      ((∫ ω, ω.2 0 ∂reducedLaw Q)⁻¹ • homogenizedCoefficient Q)

end EinsteinFull.Blueprint
