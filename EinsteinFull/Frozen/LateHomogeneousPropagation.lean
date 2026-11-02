import EinsteinFull.Proofs.LateHomogeneousPropagation
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

namespace EinsteinFull.Frozen
open EinsteinRelation

/-- Lemma 6.4, for all actual endpoints, on a fixed complex disc and every
specified growing real window. The power gain is independent of that real window. -/
theorem late_homogeneous_propagation (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
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
          Cw * Real.exp (Cw * lam ^ 2 * T) * T ^ (-(1 / 2 + (d : ℝ) / 4) - gain)) := by
  exact EinsteinFull.Proofs.late_homogeneous_propagation d hd D δ hδ hδ'

end EinsteinFull.Frozen
