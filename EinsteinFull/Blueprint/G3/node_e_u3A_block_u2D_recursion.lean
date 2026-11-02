import EinsteinFull.Blueprint.G3.LocalizedCovarianceObjects

open MeasureTheory ProbabilityTheory

namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.External.AKM

/-- Graph node `e:block-recursion`, `paper/main.tex:934–948`.
DRAFT. The children are the actual trimmed blocks in the dyadic partition of
Q₂L, with centers ±L/2 in each coordinate. Independence is joint, not merely
componentwise, and covariance includes matrix-clock cross entries.
A structural large-scale threshold precedes the law. -/
def node_e_u3A_block_u2D_recursionStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β),
    ∃ C L₀ κ : ℝ, 0 < C ∧ 2 ≤ L₀ ∧ 0 < κ ∧ κ ≤ (1 - β) / 2 ∧
    ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      HasSmoothBounds D Q →
      ∀ L : ℝ, L₀ ≤ L →
      let X := covarianceBlock d hd D s δ γ η β h Q (L ^ η) L L 0 (fun _ => 1)
      let Xm := covarianceBlock d hd D s δ γ η β h Q (L ^ η) L (L - L ^ β) 0 (fun _ => 1)
      let X₂ := covarianceBlock d hd D s δ γ η β h Q ((2 * L) ^ η) (2 * L) (2 * L) 0 (fun _ => 1)
      let children := fun j : Fin d → Fin 2 =>
        covarianceBlock d hd D s δ γ η β h Q (L ^ η) L (L - L ^ β)
          (fun i => if j i = 0 then -L / 2 else L / 2) (fun _ => 1)
      let error := fun ω a => X₂ ω a - (2 : ℝ) ^ (-(d : ℝ) / 2) *
        ∑ j : Fin d → Fin 2, children j ω a
      MemLp (fun ω => covarianceVectorSize (X ω)) 2 (reducedLaw Q) ∧
      MemLp (fun ω => covarianceVectorSize (Xm ω)) 2 (reducedLaw Q) ∧
      covarianceL2Size (reducedLaw Q) X ≤ C ∧
      covarianceL2Size (reducedLaw Q) (fun ω a => X ω a - Xm ω a) ≤
        C * L ^ (-(1 - β) / 2) ∧
      iIndepFun children (reducedLaw Q) ∧
      (∀ j, IdentDistrib (children j) Xm (reducedLaw Q) (reducedLaw Q)) ∧
      (∀ j a, Integrable (fun ω => children j ω a) (reducedLaw Q) ∧
        (∫ ω, children j ω a ∂reducedLaw Q) = 0) ∧
      MemLp (fun ω => covarianceVectorSize (error ω)) 2 (reducedLaw Q) ∧
      covarianceL2Size (reducedLaw Q) error ≤ C * L ^ (-κ) ∧
      covarianceMatrixSize (covarianceBlockMatrix (reducedLaw Q) X₂ -
        covarianceBlockMatrix (reducedLaw Q) X) ≤ C * L ^ (-κ)

end EinsteinFull.Blueprint
