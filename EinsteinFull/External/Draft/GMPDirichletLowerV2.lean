import EinsteinFull.External.Source.GMPDirichletSpectralKernel

namespace EinsteinFull.External.Draft
open EinsteinRelation EinsteinFull.External.Source.GMP

/-- Revised DRAFT for `external:GMP#5.3`, GMP Lemma5.3, printed pp.22–23.
V2 selects the actual weighted Dirichlet heat-semigroup kernel through its
complete Dirichlet spectral resolution. The estimate and every constant,
geometry, time and pole quantifier are unchanged from V1. No axiom is admitted. -/
def gmpDirichletLowerStmtV2 : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (κ R : ℝ), 0 < κ → 0 < R →
    ∀ (center : Vec d) (radius : ℝ), 0 < radius →
      euclideanNorm center + radius < R →
    ∃ C : ℝ, 0 < C ∧
      ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
        IsUniformlyElliptic κ ρ α →
      ∀ (K : ℝ → Vec d → Vec d → ℝ)
        (G : ℝ → Vec d → Vec d → Vec d),
        IsSpectralDirichletFundamentalSolution ρ α R K G →
      ∀ x ∈ sourceBall center radius, C ≤ K 1 x 0

end EinsteinFull.External.Draft
