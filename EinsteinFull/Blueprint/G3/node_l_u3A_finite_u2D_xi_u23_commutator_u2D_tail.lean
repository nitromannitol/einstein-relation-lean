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

/-- Graph node `l:finite-xi#commutator-tail`, `paper/main.tex:1109–1113`.
The identity and tail integrability are in stationary complex L², with the
actual coefficient, homogenized matrix and centered joint commutator. -/
def node_l_u3A_finite_u2D_xi_u23_commutator_u2D_tailStmt : Prop :=
  ∀ (d : ℕ) (_hd : 2 ≤ d) (D : StructuralData d),
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β →
    ∀ P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
    ∀ hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 P,
    ∀ Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q),
      IsJointObservation Q Z →
    ∃ G J : ℝ≥0 → Fin d → Fin d → Lp ℂ 2 (reducedLaw Q),
    ∃ H X : ℝ≥0 → Fin d → Fin d → Lp ℂ 2 (reducedLaw Q),
      (∀ (r : ℝ≥0) (i : Fin d), HasComplexHorizontalGradient
        (reducedLaw Q) (reducedLaw_stationary Q) (P r (β i)) (G r i)) ∧
      (∀ (r : ℝ≥0) (i j : Fin d), (J r i j : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
        fun ω => ∑ k : Fin d,
          ((ω.1 0 j k - homogenizedCoefficient Q j k : ℝ) : ℂ) * G r i k ω) ∧
      (∀ (τ : ℝ≥0) (i : Fin d),
        IsFiniteTimeCommutator Q P hP.2.2.1 β τ i (H τ i) (X τ i)) ∧
      ∀ (τ : ℝ≥0) (i j : Fin d),
        IntegrableOn (fun r : ℝ => centeredComplexLp Q (J r.toNNReal i j))
          (Set.Ici (τ : ℝ)) ∧
        centeredComplexLp Q (X τ i j) - Z (.inl (j, i)) =
          -(∫ r in Set.Ici (τ : ℝ), centeredComplexLp Q (J r.toNNReal i j))

end EinsteinFull.Blueprint
