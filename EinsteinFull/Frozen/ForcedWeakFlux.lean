import EinsteinFull.Proofs.ForcedWeakFlux
import EinsteinFull.Frozen.StructuralData
import EinsteinFull.Frozen.SmoothEnvironment
import EinsteinFull.Frozen.ReducedDriftObservation
import EinsteinFull.Frozen.ReducedCoefficientObservation
import EinsteinFull.Frozen.ReducedClockObservation
import EinsteinFull.Frozen.ComplexEnvironmentSemigroup
import EinsteinFull.Frozen.ComplexTransposeSemigroup
import EinsteinFull.Frozen.EndpointWeakFlux
import EinsteinFull.Frozen.CenteredComplexLp
import EinsteinFull.Frozen.GaussianDerivativeAverage
import EinsteinFull.Frozen.StationarySchwartzAverage
import EinsteinFull.Frozen.GaussianTestControl

open MeasureTheory
open scoped NNReal ENNReal
namespace EinsteinFull.Frozen
open EinsteinRelation

/-- Lemma 4.4 on the actual endpoints and actual weak fluxes. Only the source's
finite-p endpoint moment estimate is a premise of the estimate; joint locality
is supplied by the standing finite-range environment and actual semigroup.
Both the Gaussian derivative and smooth-test versions are included. -/
theorem forced_weak_flux (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ ε η₀ : ℝ, ∃ L : ℕ → ℕ, 0 < ε ∧ 0 < η₀ ∧
    ∀ p : ℝ, 2 ≤ p → ∃ growth₀ t₀ : ℝ, ∃ Cder : ℕ → ℝ,
      0 < growth₀ ∧ 1 ≤ t₀ ∧ (∀ k, 0 < Cder k) ∧
    (      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
        (hQ : HasSmoothBounds D Q)
        (β : Fin d → Lp ℂ 2 (reducedLaw Q))
        (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
        IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
        IsReducedClockObservation Q μ → ∀ ζ : ℂ,
      ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
        IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
        IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
      ∃ G J : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
        (∀ t : ℝ≥0, 0 < (t : ℝ) →
          IsEndpointWeakFlux hd Q ν ζ a (indexedEndpoint hd Q ν ζ P Pdag β a μ t)
            (G t) (J t)) ∧
        ∀ (t : ℝ≥0), t₀ ≤ (t : ℝ) →
        ‖ζ‖ * Real.sqrt (t : ℝ) ≤ (t : ℝ) ^ η₀ →
        ∀ growth K : ℝ, growth₀ ≤ growth → 1 ≤ K →
        MemLp (indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8) : FieldPair d → ℂ)
          (ENNReal.ofReal p) (reducedLaw Q) →
        (eLpNorm (indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8) : FieldPair d → ℂ)
          (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
          K * Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 8) *
            (((t : ℝ) / 8) ^ (-(1 / 2 + (d : ℝ) / 4)) +
              ‖ζ‖ * ((t : ℝ) / 8) ^ (-(d : ℝ) / 4)) →
        ∀ (s : ℝ), 1 ≤ s → ∀ hs : 0 < s,
        ∀ (k : ℕ) (dirs : Fin k → Fin d),
          (∀ j : Fin d, MemLp
            (gaussianDerivativeAverage hd Q s hs k dirs (centeredComplexLp Q (J t j)) :
              FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)) ∧
          Real.sqrt (∑ j : Fin d, ((eLpNorm
            (gaussianDerivativeAverage hd Q s hs k dirs (centeredComplexLp Q (J t j)) :
              FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal) ^ 2) ≤
            Cder k * K * Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 2) *
              (t : ℝ) ^ (-1 - ε) * s ^ (-(d : ℝ) / 4 - (k : ℝ) / 2) *
                (1 + (t : ℝ) / s) ^ L k) ∧
    (∀ ctest : ℝ, 0 < ctest → ∀ Btest : ℕ → ℝ, (∀ q, 0 < Btest q) →
      ∃ ttest : ℝ, ∃ Ctest : ℕ → ℝ, t₀ ≤ ttest ∧ (∀ k, 0 < Ctest k) ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
        (hQ : HasSmoothBounds D Q)
        (β : Fin d → Lp ℂ 2 (reducedLaw Q))
        (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
        IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
        IsReducedClockObservation Q μ → ∀ ζ : ℂ,
      ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
        IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
        IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
      ∃ G J : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
        (∀ t : ℝ≥0, 0 < (t : ℝ) →
          IsEndpointWeakFlux hd Q ν ζ a (indexedEndpoint hd Q ν ζ P Pdag β a μ t)
            (G t) (J t)) ∧
        ∀ (t : ℝ≥0), ttest ≤ (t : ℝ) →
        ‖ζ‖ * Real.sqrt (t : ℝ) ≤ (t : ℝ) ^ η₀ →
        ∀ growth K : ℝ, growth₀ ≤ growth → 1 ≤ K →
        MemLp (indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8) : FieldPair d → ℂ)
          (ENNReal.ofReal p) (reducedLaw Q) →
        (eLpNorm (indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8) : FieldPair d → ℂ)
          (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
          K * Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 8) *
            (((t : ℝ) / 8) ^ (-(1 / 2 + (d : ℝ) / 4)) +
              ‖ζ‖ * ((t : ℝ) / 8) ^ (-(d : ℝ) / 4)) →
        ∀ (s : ℝ), 1 ≤ s → ∀ (k : ℕ) (ψ : SchwartzMap (Vec d) ℂ),
        HasGaussianTestControl s k ctest Btest ψ →
          (∀ j : Fin d, MemLp
            (stationarySchwartzAverage Q ψ (centeredComplexLp Q (J t j)) : FieldPair d → ℂ)
              (ENNReal.ofReal p) (reducedLaw Q)) ∧
          Real.sqrt (∑ j : Fin d, ((eLpNorm
            (stationarySchwartzAverage Q ψ (centeredComplexLp Q (J t j)) : FieldPair d → ℂ)
              (ENNReal.ofReal p) (reducedLaw Q)).toReal) ^ 2) ≤
            Ctest k * K * Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 2) *
              (t : ℝ) ^ (-1 - ε) * s ^ (-(d : ℝ) / 4 - (k : ℝ) / 2) *
                (1 + (t : ℝ) / s) ^ L k) := by
  exact EinsteinFull.Proofs.forced_weak_flux d hd D

end EinsteinFull.Frozen
