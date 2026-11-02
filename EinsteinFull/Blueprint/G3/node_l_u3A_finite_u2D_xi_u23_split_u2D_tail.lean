import EinsteinFull.Frozen.StructuralData
import EinsteinFull.Frozen.SmoothEnvironment
import EinsteinFull.Frozen.ReducedDriftObservation
import EinsteinFull.Frozen.ReducedCoefficientObservation
import EinsteinFull.Frozen.ReducedClockObservation
import EinsteinFull.Frozen.FiniteTimeCommutator
import EinsteinFull.Frozen.JointObservation
import EinsteinFull.Frozen.CenteredComplexLp
import EinsteinFull.Frozen.GaussianDerivativeAverage
import EinsteinFull.Frozen.FiniteTimeFlux
import EinsteinFull.Frozen.ComplexTransposeSemigroup
import EinsteinFull.Frozen.EndpointDriftSign
import EinsteinFull.Frozen.HomogeneousDerivativeAverage
import EinsteinFull.Frozen.ModelVelocityEndpoint
import EinsteinFull.Frozen.ModelTransposeEndpoint

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Graph node `l:finite-xi#split-tail`, `paper/main.tex:1114–1124`.
Actual centered commutator tail split at s^(1+nu), followed by a single gain
for every fixed kernel derivative. All integrals are stationary complex L². -/
def node_l_u3A_finite_u2D_xi_u23_split_u2D_tailStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ ε L₀ ν gain t₀ : ℝ, ∃ Cder : ℕ → ℝ,
      0 < ε ∧ 0 < L₀ ∧ 0 < ν ∧ ν < ε / (4 * L₀) ∧
      0 < gain ∧ gain ≤ ε ∧ gain ≤ ε / 2 ∧ gain ≤ ν * (d : ℝ) / 4 ∧
      1 ≤ t₀ ∧ (∀ k, 0 < Cder k) ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsJointObservation Q Z →
    ∀ P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
    ∀ hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 P,
    ∃ G J H X : ℝ≥0 → Fin d → Fin d → Lp ℂ 2 (reducedLaw Q),
      (∀ r i, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (P r (β i)) (G r i)) ∧
      (∀ r i j, (J r i j : FieldPair d → ℂ) =ᵐ[reducedLaw Q] fun ω =>
        ∑ k : Fin d, ((ω.1 0 j k - homogenizedCoefficient Q j k : ℝ) : ℂ) * G r i k ω) ∧
      (∀ τ i, IsFiniteTimeCommutator Q P hP.2.2.1 β τ i (H τ i) (X τ i)) ∧
      ∀ τ : ℝ≥0, t₀ ≤ (τ : ℝ) →
      (∀ (s : ℝ), (τ : ℝ) ≤ s → ∀ hs : 0 < s, ∀ i : Fin d,
        (∀ j, IntegrableOn (fun r : ℝ => centeredComplexLp Q (J r.toNNReal i j))
          (Set.Ici (τ : ℝ))) ∧
        Real.sqrt (∑ j : Fin d, ‖gaussianAverage hd Q s hs
          (∫ r in Set.Icc (τ : ℝ) (s ^ (1 + ν)),
            centeredComplexLp Q (J r.toNNReal i j))‖ ^ 2) ≤
          Cder 0 * s ^ (-(d : ℝ) / 4) *
            ((τ : ℝ) ^ (-ε) + s ^ (-ε / 2)) ∧
        Real.sqrt (∑ j : Fin d, ‖gaussianAverage hd Q s hs
          (∫ r in Set.Ici (s ^ (1 + ν)),
            centeredComplexLp Q (J r.toNNReal i j))‖ ^ 2) ≤
          Cder 0 * s ^ (-(d : ℝ) / 4) * s ^ (-ν * (d : ℝ) / 4) ∧
        Real.sqrt (∑ j : Fin d, ‖gaussianAverage hd Q s hs
          (centeredComplexLp Q (X τ i j) - Z (.inl (j,i)))‖ ^ 2) ≤
          Cder 0 * (τ : ℝ) ^ (-gain) * s ^ (-(d : ℝ) / 4)) ∧
      ∀ (s : ℝ), 2 * (τ : ℝ) ≤ s → ∀ hs : 0 < s,
      ∀ (i : Fin d) (k : ℕ) (dirs : Fin k → Fin d),
        Real.sqrt (∑ j : Fin d, ‖gaussianDerivativeAverage hd Q s hs k dirs
          (centeredComplexLp Q (X τ i j) - Z (.inl (j,i)))‖ ^ 2) ≤
          Cder k * (τ : ℝ) ^ (-gain) * s ^ (-(d : ℝ) / 4 - (k : ℝ) / 2)

end EinsteinFull.Blueprint
