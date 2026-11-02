import EinsteinFull.Blueprint.Roots.node_t_u3A_expansion

open MeasureTheory Filter
open scoped Topology NNReal BigOperators

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Graph node `t.main#elementary-rate`, `paper/main.tex:1431–1433`.
A common structural threshold and rate apply to both force signs. The full
expansion is an internal dependency, not an additional statement assumption. -/
def node_t_u2E_main_u23_elementary_u2D_rateStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ C lamStar : ℝ, 0 ≤ C ∧ 0 < lamStar ∧ lamStar ≤ Real.exp (-1) ∧
      (∀ s : ℝ, 0 < s → s ≤ lamStar →
        s ^ d * (1 + Real.log (1 / s)) ≤ C * s) ∧
      ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
        HasSmoothBounds D Q →
        ∀ X : DiffusionFamily d,
          IsSignedPhysicalFamily (⟨0, by omega⟩ : Fin d) Q X →
          ∀ covariance : Mat d,
            HasDiffusivity Q.measure (originLaw (X 0)) covariance →
            ∀ (lam : ℝ), 0 < |lam| → |lam| ≤ lamStar →
              ∀ velocity : Vec d,
                HasQuenchedVelocity Q.measure (originLaw (X lam)) velocity →
                euclideanNorm ((lam⁻¹ • velocity) -
                  covariance.mulVec (unitVector (⟨0, by omega⟩ : Fin d))) ≤ C * |lam|

end EinsteinFull.Blueprint
