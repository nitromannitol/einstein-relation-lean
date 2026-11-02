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

/-- Graph node `l:finite-xi#potential-identification`, `paper/main.tex:1108–1113`.
The actual finite-time corrector gradients converge coordinatewise in L² to
the real variational potential corrector gradient embedded in complex L².
No scalar corrector limit is asserted. -/
def node_l_u3A_finite_u2D_xi_u23_potential_u2D_identificationStmt : Prop :=
  ∀ (d : ℕ) (_hd : 2 ≤ d) (D : StructuralData d),
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β →
    ∀ P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
    ∀ hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 P,
    ∃ G : ℝ≥0 → Fin d → Fin d → Lp ℂ 2 (reducedLaw Q),
      (∀ (r : ℝ≥0) (i : Fin d), HasComplexHorizontalGradient
        (reducedLaw Q) (reducedLaw_stationary Q) (P r (β i)) (G r i)) ∧
      ∀ i : Fin d, ∃ L : Fin d → Lp ℂ 2 (reducedLaw Q),
        (∀ j : Fin d, (L j : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
          fun ω => (correctorGradient Q i ω j : ℂ)) ∧
        (∀ (τ : ℝ≥0), HasComplexHorizontalGradient
          (reducedLaw Q) (reducedLaw_stationary Q)
          (finiteTimeCorrector Q P hP.2.2.1 β τ i)
          (fun j => ∫ r in Set.Icc (0 : ℝ) (τ : ℝ), G r.toNNReal i j)) ∧
        ∀ j : Fin d,
          IntegrableOn (fun r : ℝ => G r.toNNReal i j) (Set.Ici 0) ∧
          (∫ r in Set.Ici (0 : ℝ), G r.toNNReal i j) = L j ∧
          Tendsto (fun τ : ℝ => ∫ r in Set.Icc (0 : ℝ) τ, G r.toNNReal i j)
            atTop (𝓝 (L j))

end EinsteinFull.Blueprint
