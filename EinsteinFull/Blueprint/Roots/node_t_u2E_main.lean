import EinsteinFull.Frozen.StructuralData
import EinsteinFull.Frozen.SmoothEnvironment
import EinsteinFull.Frozen.SignedPhysicalFamily

open MeasureTheory

namespace EinsteinFull.Blueprint

open EinsteinRelation

/-- Exact statement mirror of `t.main`; frozen declaration
`EinsteinFull.Frozen.mobility_rate`, source `paper/main.tex:136–144`.
No anchor import or conclusion-bearing premise is used. -/
def node_t_u2E_mainStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ C lamStar : ℝ, 0 ≤ C ∧ 0 < lamStar ∧
      ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      HasSmoothBounds D Q →
      ∀ P : DiffusionFamily d,
      IsSignedPhysicalFamily (⟨0, by omega⟩ : Fin d) Q P →
      ∀ covariance : Mat d,
      HasDiffusivity Q.measure (originLaw (P 0)) covariance →
      ∀ (lam : ℝ), 0 < lam → lam ≤ lamStar →
      ∀ velocity : Vec d,
      HasQuenchedVelocity Q.measure (originLaw (P lam)) velocity →
        euclideanNorm ((lam⁻¹ • velocity) -
          covariance.mulVec (unitVector (⟨0, by omega⟩ : Fin d))) ≤ C * lam

end EinsteinFull.Blueprint
