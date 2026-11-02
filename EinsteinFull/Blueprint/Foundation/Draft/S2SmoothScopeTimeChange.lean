import EinsteinFull.Frozen.ReducedClockRate
import EinsteinFull.Frozen.SignedPhysicalFamily
import EinsteinFull.Frozen.HomogenizedCoefficient
import EinsteinFull.Frozen.SmoothWithBounds

open MeasureTheory Filter
open scoped Topology NNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- DRAFT smooth-scope V2 of `node_eq_u2E_time_u2D_change_u2D_identitiesStmt`, paper/main.tex:227–232.
Only the law's Assumption 1.2 smoothness block is added; all following hypotheses
and conclusions are byte-identical to V1. Signed forces, full anisotropic matrix,
a.e. qualifiers, actual laws and inverse clock remain literal. The full time-change
statement retains the Lambda0-first bound, before dimension and derivative data.
Not elaborated or reviewed yet; not imported by production; no V1/root replacement. -/
def node_eq_u2E_time_u2D_change_u2D_identitiesStmtV2 : Prop :=
  ∀ Λ₀ : ℝ, 1 ≤ Λ₀ → ∃ Λ : ℝ, 1 ≤ Λ ∧
    ∀ (d : ℕ) (hd : 2 ≤ d) (r₀ : ℝ) (b : ℕ → ℝ)
    (Q : EnvironmentLaw d Λ₀ r₀),
    1 ≤ r₀ → (∀ k : ℕ, 1 ≤ k → 0 < b k) →
    (∀ᵐ ω ∂Q.measure, IsSmoothWithBounds b ω) →
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
