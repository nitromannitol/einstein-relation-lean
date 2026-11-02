import EinsteinFull.Frozen.StructuralData
import EinsteinFull.Frozen.SmoothEnvironment
import EinsteinFull.Frozen.ExpansionModulus
import EinsteinFull.Frozen.CriticalVelocityTerm
import EinsteinFull.Frozen.SignedPhysicalFamily

open MeasureTheory
open scoped BigOperators

namespace EinsteinFull.Blueprint

open EinsteinRelation

/-- Exact statement mirror of `t:expansion`; frozen declaration
`EinsteinFull.Frozen.uniform_small_force_expansion`, source `paper/main.tex:122–134`.
No anchor import or conclusion-bearing premise is used. -/
def node_t_u3A_expansionStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ C lamStar : ℝ, 0 ≤ C ∧ 0 < lamStar ∧
      ∃ hstar : lamStar ≤ Real.exp (-1),
      ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      HasSmoothBounds D Q →
      ∃ (b : Fin (d + 1) → Vec d) (c : Vec d),
        (∑ j, euclideanNorm (b j)) + euclideanNorm c ≤ C ∧
        ∀ P : DiffusionFamily d,
        IsSignedPhysicalFamily (⟨0, by omega⟩ : Fin d) Q P →
        ∀ covariance : Mat d,
        HasDiffusivity Q.measure (originLaw (P 0)) covariance →
          b ⟨0, by omega⟩ = covariance.mulVec (unitVector (⟨0, by omega⟩ : Fin d)) ∧
          ∀ velocity : ℝ → Vec d,
          (∀ lam : ℝ, lam ≠ 0 →
            HasQuenchedVelocity Q.measure (originLaw (P lam)) (velocity lam)) →
          ∀ (lam : ℝ) (hlam : 0 < |lam|) (hsmall : |lam| ≤ lamStar),
            euclideanNorm (velocity lam - (∑ j : Fin (d + 1), lam ^ (j.val + 1) • b j) -
              criticalVelocityTerm d lam (abs_pos.mp hlam) • c) ≤
              C * |lam| ^ (d + 1) *
                expansionModulus |lam| hlam (hsmall.trans hstar)

end EinsteinFull.Blueprint
