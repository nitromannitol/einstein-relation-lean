import EinsteinFull.Frozen.StructuralData
import EinsteinFull.Frozen.SmoothEnvironment
import EinsteinFull.Frozen.ReducedDriftObservation
import EinsteinFull.Frozen.ReducedCoefficientObservation
import EinsteinFull.Frozen.ReducedClockObservation
import EinsteinFull.Frozen.ComplexEnvironmentSemigroup
import EinsteinFull.Frozen.ComplexTransposeSemigroup
import EinsteinFull.Frozen.IndexedEndpoint
import EinsteinFull.Frozen.EndpointDriftSign
import EinsteinFull.Frozen.HomogeneousAverage

open MeasureTheory
open scoped NNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Exact statement mirror of `l:late-propagation`; frozen declaration
`EinsteinFull.Frozen.late_homogeneous_propagation`, source `paper/main.tex:1129–1137`.
No anchor import or conclusion-bearing premise is used. -/
def node_l_u3A_late_u2D_propagationStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 2),
    ∃ gain C T₀ : ℝ, 0 < gain ∧ 0 < C ∧ 2 ≤ T₀ ∧
    (∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ T : ℝ, ∀ hT : 1 < T,
      T₀ ≤ T → ∀ ζ : ℂ, ‖ζ‖ * Real.sqrt T ≤ 2 →
      ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag →
      ∀ ν : EndpointIndex d,
        ‖indexedEndpoint hd Q ν ζ P Pdag β a μ T.toNNReal -
          homogeneousAverage Q ⟨0, by omega⟩ (T - T ^ (1 - δ)) (by have := Real.rpow_lt_self_of_one_lt hT (show 1 - δ < 1 by linarith); linarith)
            ((endpointDriftSign ν : ℂ) * ζ)
            (indexedEndpoint hd Q ν ζ P Pdag β a μ (T ^ (1 - δ)).toNNReal)‖ ≤
          C * Real.exp (C * ‖ζ‖ ^ 2 * T) * T ^ (-(1 / 2 + (d : ℝ) / 4) - gain)) ∧
    (∀ C₀ : ℝ, 0 < C₀ → ∃ Cw Tw : ℝ, 0 < Cw ∧ 2 ≤ Tw ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ T : ℝ, ∀ hT : 1 < T,
      Tw ≤ T → ∀ lam : ℝ,
      |lam| * Real.sqrt T ≤ C₀ * Real.log T ^ (1 / 4 : ℝ) →
      ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ (lam : ℂ) P →
      IsComplexTransposeSemigroup Q P Pdag →
      ∀ ν : EndpointIndex d,
        ‖indexedEndpoint hd Q ν (lam : ℂ) P Pdag β a μ T.toNNReal -
          homogeneousAverage Q ⟨0, by omega⟩ (T - T ^ (1 - δ)) (by have := Real.rpow_lt_self_of_one_lt hT (show 1 - δ < 1 by linarith); linarith)
            ((endpointDriftSign ν : ℂ) * (lam : ℂ))
            (indexedEndpoint hd Q ν (lam : ℂ) P Pdag β a μ (T ^ (1 - δ)).toNNReal)‖ ≤
          Cw * Real.exp (Cw * lam ^ 2 * T) * T ^ (-(1 / 2 + (d : ℝ) / 4) - gain))

end EinsteinFull.Blueprint
