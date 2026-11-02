import EinsteinFull.Blueprint.G3.LocalizedCovarianceObjects

open MeasureTheory ProbabilityTheory

namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.External.AKM

/-- Graph node `e:block-change`, `paper/main.tex:921–926`.
DRAFT. One positive structural scale-change exponent works for all joint
coordinates. The difference uses the same actual selected source family.
The structural threshold accommodates the literal source construction r≥2. -/
def node_e_u3A_block_u2D_changeStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β),
    ∃ C L₀ κ₀ : ℝ, 0 < C ∧ 2 ≤ L₀ ∧ 0 < κ₀ ∧ κ₀ ≤ (1 - β) / 2 ∧
    ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      HasSmoothBounds D Q →
      ∀ (L : ℝ), L₀ ≤ L → ∀ (x : Vec d) (r : ℝ),
        L ^ η ≤ r → r ≤ L ^ β →
        let X := fun ω a => covarianceBlock d hd D s δ γ η β h Q r L L x (fun _ => 1) ω a -
          covarianceBlock d hd D s δ γ η β h Q (L ^ η) L L x (fun _ => 1) ω a
        MemLp (fun ω => covarianceVectorSize (X ω)) 2 (reducedLaw Q) ∧
        covarianceL2Size (reducedLaw Q) X ≤ C * L ^ (-κ₀)

end EinsteinFull.Blueprint
