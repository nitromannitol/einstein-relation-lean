import EinsteinFull.Proofs.ForcedLocalEstimates
import EinsteinFull.Frozen.StructuralData
import EinsteinFull.Frozen.SmoothEnvironment
import EinsteinFull.Frozen.ReducedDriftObservation
import EinsteinFull.Frozen.ReducedCoefficientObservation
import EinsteinFull.Frozen.ReducedClockObservation
import EinsteinFull.Frozen.ComplexEnvironmentSemigroup
import EinsteinFull.Frozen.ComplexTransposeSemigroup
import EinsteinFull.Frozen.ComplexHorizontalGradient
import EinsteinFull.Frozen.UncenteredEndpoint
import EinsteinFull.Frozen.ComplexLocalObservation
import EinsteinFull.Frozen.LocalSpatialEnergy
import EinsteinFull.Frozen.CubeIntegralObservation
import EinsteinFull.Frozen.GaussianAverage
import Mathlib.Analysis.Calculus.Deriv.Basic

open MeasureTheory
open scoped NNReal ENNReal
namespace EinsteinFull.Frozen
open EinsteinRelation

/-- Lemma 4.3: actual horizontal/time derivatives, normalized local energy,
Holder averaging, joint local approximants and deterministic rare-event bounds.
The pointwise gradient locality conclusion is the smooth unit-interior-estimate
version in the source proof; it implies the stated local L2 gradient version. -/
theorem forced_local_estimates (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ α Cdet c : ℝ, ∃ N : ℕ, 0 < α ∧ 1 ≤ Cdet ∧ 0 < c ∧
    ∀ p : ℝ, 2 ≤ p → ∃ C Cp : ℝ,
      1 ≤ C ∧ 0 < Cp ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
    ∃ G : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
    ∃ V : ℝ≥0 → Lp ℂ 2 (reducedLaw Q),
    (∀ t : ℝ≥0, 0 < (t : ℝ) →
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (indexedEndpoint hd Q ν ζ P Pdag β a μ t) (G t) ∧
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (uncenteredEndpoint hd Q ν ζ P Pdag β a μ t) (G t) ∧
      HasDerivAt (fun r : ℝ => indexedEndpoint hd Q ν ζ P Pdag β a μ r.toNNReal)
        (V t) (t : ℝ)) ∧
    (∀ (t : ℝ≥0) (ht : 0 < (t : ℝ)),
      let U := indexedEndpoint hd Q ν ζ P Pdag β a μ t
      let U₈ := indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8)
      MemLp (U₈ : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧
      (∀ (ρ : ℝ) (x : Vec d) (hρ : Real.sqrt (t : ℝ) ≤ ρ),
        MemLp (localSpatialEnergy Q t ρ (lt_of_lt_of_le (Real.sqrt_pos.mpr ht) hρ) x (G t) (V t)) (ENNReal.ofReal p) (reducedLaw Q) ∧
        (eLpNorm (localSpatialEnergy Q t ρ (lt_of_lt_of_le (Real.sqrt_pos.mpr ht) hρ) x (G t) (V t))
          (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        C * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ C * (t : ℝ) ^ (-(1 / 2 : ℝ)) *
          Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) *
          (eLpNorm (U₈ : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal) ∧
      (∀ b : ℝ, 0 < b → b ≤ 1 / 16 → ∀ hbt : 0 < b * (t : ℝ),
        MemLp ((U - gaussianAverage hd Q (b * (t : ℝ)) hbt U) : FieldPair d → ℂ)
          (ENNReal.ofReal p) (reducedLaw Q) ∧
        (eLpNorm ((U - gaussianAverage hd Q (b * (t : ℝ)) hbt U) : FieldPair d → ℂ)
          (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
          C * b ^ (α / 2) * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ C *
            Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) *
            (eLpNorm (U₈ : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal)) ∧
    (∀ t : ℝ≥0, 1 ≤ (t : ℝ) → ∀ ρ : ℝ, Cdet * Real.sqrt (t : ℝ) ≤ ρ →
      ∃ Uloc : Lp ℂ 2 (reducedLaw Q), ∃ Gloc : Fin d → Lp ℂ 2 (reducedLaw Q),
      IsComplexLocalObservation Q ρ Uloc ∧
      (∀ j, IsComplexLocalObservation Q ρ (Gloc j)) ∧
      (∀ᵐ ω ∂reducedLaw Q,
        ‖uncenteredEndpoint hd Q ν ζ P Pdag β a μ t ω - Uloc ω‖ +
          Real.sqrt (∑ j : Fin d, ‖G t j ω - Gloc j ω‖ ^ 2) ≤
        Cdet * (2 + (t : ℝ)) ^ N * Real.exp (Cdet * ‖ζ‖ ^ 2 * (t : ℝ) - c * ρ ^ 2 / (t : ℝ))) ∧
      (∀ᵐ ω ∂reducedLaw Q,
        ‖centeredComplexLp Q (uncenteredEndpoint hd Q ν ζ P Pdag β a μ t) ω -
          centeredComplexLp Q Uloc ω‖ ≤
        2 * Cdet * (2 + (t : ℝ)) ^ N *
          Real.exp (Cdet * ‖ζ‖ ^ 2 * (t : ℝ) - c * ρ ^ 2 / (t : ℝ))) ∧
      ∃ Ucube : Lp ℂ 2 (reducedLaw Q), ∃ Gcube : Fin d → Lp ℂ 2 (reducedLaw Q),
        IsComplexLocalObservation Q (((d : ℝ) + 1) * ρ) Ucube ∧
        (∀ j, IsComplexLocalObservation Q (((d : ℝ) + 1) * ρ) (Gcube j)) ∧
        ∀ᵐ ω ∂reducedLaw Q,
          ‖cubeIntegralObservation Q ρ (uncenteredEndpoint hd Q ν ζ P Pdag β a μ t) ω - Ucube ω‖ +
          Real.sqrt (∑ j : Fin d,
            ‖cubeIntegralObservation Q ρ (G t j) ω - Gcube j ω‖ ^ 2) ≤
          Cdet * (2 + (t : ℝ) + ρ) ^ (N + d) *
            Real.exp (Cdet * ‖ζ‖ ^ 2 * (t : ℝ) - c * ρ ^ 2 / (t : ℝ))) ∧
    (∀ t : ℝ≥0, 0 < (t : ℝ) → ‖ζ‖ ≤ 4 → ∀ᵐ ω ∂reducedLaw Q,
      ‖uncenteredEndpoint hd Q ν ζ P Pdag β a μ t ω‖ +
        Real.sqrt (∑ j : Fin d, ‖G t j ω‖ ^ 2) ≤
      Cdet * (2 + (t : ℝ)) ^ N * Real.exp (Cdet * ‖ζ‖ ^ 2 * (t : ℝ))) := by
  exact EinsteinFull.Proofs.forced_local_estimates d hd D

end EinsteinFull.Frozen
