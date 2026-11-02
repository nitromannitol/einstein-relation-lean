import EinsteinFull.Frozen.StructuralData
import EinsteinFull.Frozen.SmoothEnvironment
import EinsteinFull.Frozen.ReducedDriftObservation
import EinsteinFull.Frozen.FiniteTimeCommutator
import EinsteinFull.Frozen.JointObservation
import EinsteinFull.Frozen.CenteredComplexLp

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Graph node `l:finite-xi#gradient-limit`, `paper/main.tex:1108–1113`.
Integrability and convergence concern gradients only, also in dimension two.
The limit is not identified with a corrector in this node. -/
def node_l_u3A_finite_u2D_xi_u23_gradient_u2D_limitStmt : Prop :=
  ∀ (d : ℕ) (_hd : 2 ≤ d) (D : StructuralData d),
    ∃ C : ℝ, 0 < C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β →
    ∀ P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
    ∀ hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 P,
    ∃ G : ℝ≥0 → Fin d → Fin d → Lp ℂ 2 (reducedLaw Q),
      (∀ (r : ℝ≥0) (i : Fin d), HasComplexHorizontalGradient
        (reducedLaw Q) (reducedLaw_stationary Q) (P r (β i)) (G r i)) ∧
      (∀ (r : ℝ≥0), 1 ≤ (r : ℝ) → ∀ i : Fin d,
        Real.sqrt (∑ j : Fin d, ‖G r i j‖ ^ 2) ≤
          C * (r : ℝ) ^ (-1 - (d : ℝ) / 4)) ∧
      ∀ i : Fin d,
        (∀ j : Fin d, IntegrableOn (fun r : ℝ => G r.toNNReal i j) (Set.Ici 0)) ∧
        ∃ L : Fin d → Lp ℂ 2 (reducedLaw Q), ∀ j : Fin d,
          Tendsto (fun τ : ℝ => ∫ r in Set.Icc (0 : ℝ) τ, G r.toNNReal i j)
            atTop (𝓝 (L j))

end EinsteinFull.Blueprint
