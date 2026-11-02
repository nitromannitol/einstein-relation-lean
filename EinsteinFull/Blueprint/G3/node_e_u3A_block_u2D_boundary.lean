import EinsteinFull.Blueprint.G3.LocalizedCovarianceObjects

open MeasureTheory ProbabilityTheory

namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.External.AKM

/-- Graph node `e:block-boundary`, `paper/main.tex:916–920`.
DRAFT. The test vanishes in the inner cube; the block normalization still uses
L, rather than the strip volume.
The structural threshold accommodates the literal source construction r≥2. -/
def node_e_u3A_block_u2D_boundaryStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β),
    ∃ C L₀ : ℝ, 0 < C ∧ 2 ≤ L₀ ∧
    ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      HasSmoothBounds D Q →
      ∀ (L : ℝ), L₀ ≤ L → ∀ (x : Vec d) (f : Vec d → ℝ) (b : ℝ),
        Measurable f → 0 ≤ b → (∀ y ∈ clockBlockCube x L, |f y| ≤ b) →
        (∀ y ∈ clockBlockCube x (L - L ^ β), f y = 0) →
        let X := covarianceBlock d hd D s δ γ η β h Q (L ^ η) L L x f
        MemLp (fun ω => covarianceVectorSize (X ω)) 2 (reducedLaw Q) ∧
        covarianceL2Size (reducedLaw Q) X ≤ C * L ^ (-(1 - β) / 2) * b

end EinsteinFull.Blueprint
