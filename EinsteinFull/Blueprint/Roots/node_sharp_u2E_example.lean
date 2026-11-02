import EinsteinFull.Frozen.SmoothEnvironment
import EinsteinFull.Frozen.SignedPhysicalFamily

open MeasureTheory Filter
open scoped Topology

namespace EinsteinFull.Blueprint

open EinsteinRelation

/-- Exact statement mirror of `sharp.example`; frozen declaration
`EinsteinFull.Frozen.sharp_example`, source `paper/main.tex:1439–1445`.
No anchor import or conclusion-bearing premise is used. -/
def node_sharp_u2E_exampleStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d),
    ∃ (D : StructuralData d) (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q ∧ ∃ c₀ : ℝ, 0 < c₀ ∧
        ∀ P : DiffusionFamily d,
        IsSignedPhysicalFamily (⟨0, by omega⟩ : Fin d) Q P →
        ∀ covariance : Mat d,
        HasDiffusivity Q.measure (originLaw (P 0)) covariance →
        ∀ velocity : ℝ → Vec d,
        (∀ lam : ℝ, 0 < lam →
          HasQuenchedVelocity Q.measure (originLaw (P lam)) (velocity lam)) →
          Tendsto (fun lam : ℝ =>
            dot ((lam⁻¹ • velocity lam) -
              covariance.mulVec (unitVector (⟨0, by omega⟩ : Fin d)))
              (unitVector (⟨0, by omega⟩ : Fin d)) / lam)
            (𝓝[>] (0 : ℝ)) (𝓝 c₀)

end EinsteinFull.Blueprint
