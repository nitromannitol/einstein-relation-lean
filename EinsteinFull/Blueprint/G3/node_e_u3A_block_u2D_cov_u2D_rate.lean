import EinsteinFull.Blueprint.G3.LocalizedCovarianceObjects

open MeasureTheory ProbabilityTheory

namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.External.AKM

/-- Graph node `e:block-cov-rate`, `paper/main.tex:949–955`.
DRAFT. The covariance is the entrywise limit of the actual dyadic full-block
covariances. PSD, Frobenius boundedness and both rates are conclusions.
Full and trimmed blocks share the normalization L^(-d/2). -/
def node_e_u3A_block_u2D_cov_u2D_rateStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β),
    ∃ C L₀ κ : ℝ, 0 < C ∧ 2 ≤ L₀ ∧ 0 < κ ∧
    ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      HasSmoothBounds D Q →
      let A := covarianceDyadicLimit d hd D s δ γ η β h Q
      A.PosSemidef ∧ covarianceMatrixSize A ≤ C ∧
      (∀ a b, Filter.Tendsto (fun n : ℕ =>
        covarianceBlockMatrix (reducedLaw Q)
          (covarianceBlock d hd D s δ γ η β h Q (((2 : ℝ) ^ n) ^ η)
            ((2 : ℝ) ^ n) ((2 : ℝ) ^ n) 0 (fun _ => 1)) a b)
          Filter.atTop (nhds (A a b))) ∧
      ∀ n : ℕ, L₀ ≤ (2 : ℝ) ^ n →
      let L := (2 : ℝ) ^ n
      let X := covarianceBlock d hd D s δ γ η β h Q (L ^ η) L L 0 (fun _ => 1)
      let Xm := covarianceBlock d hd D s δ γ η β h Q (L ^ η) L (L - L ^ β) 0 (fun _ => 1)
      covarianceMatrixSize (covarianceBlockMatrix (reducedLaw Q) X - A) +
        covarianceMatrixSize (covarianceBlockMatrix (reducedLaw Q) Xm - A) ≤
          C * L ^ (-κ)

end EinsteinFull.Blueprint
