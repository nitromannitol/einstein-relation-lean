import EinsteinFull.Frozen.FiniteTimeFluxObservation
import EinsteinFull.Frozen.ComplexHorizontalGradient
import EinsteinFull.Frozen.ReducedLawStationary
import EinsteinFull.Frozen.IndexedEndpoint

open MeasureTheory
open scoped NNReal

namespace EinsteinFull
open EinsteinRelation

/-- The full horizontal gradient and literal finite-time flux identities.
This meaning predicate contains no norm, locality or decay estimate. -/
def IsFiniteTimeFlux {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (G F : ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q)) : Prop :=
  ∃ hG : ∀ (ν : FluxIndex d) (k : Fin d), Continuous (fun r : ℝ≥0 => G r ν k),
    ∃ hU : ∀ f : Lp ℂ 2 (reducedLaw Q), Continuous (fun r : ℝ≥0 => Pdag r f),
    (∀ (τ : ℝ≥0) (ν : FluxIndex d),
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (indexedEndpoint hd Q (ν.elim Sum.inl (fun _ => Sum.inr true)) ζ P Pdag β a μ τ)
        (G τ ν)) ∧
    ∀ (τ : ℝ≥0) (ν : FluxIndex d) (j : Fin d),
      (F τ ν j : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
        finiteTimeFluxObservation hd Q ν ζ Pdag β a G τ hG hU j

end EinsteinFull
