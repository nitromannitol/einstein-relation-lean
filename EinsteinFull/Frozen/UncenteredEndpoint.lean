import EinsteinFull.Frozen.IndexedEndpoint

open MeasureTheory
open scoped NNReal
namespace EinsteinFull
open EinsteinRelation

/-- The uncentered scalar underlying each displayed stationary endpoint. -/
noncomputable def uncenteredEndpoint {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (ν : EndpointIndex d) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (t : ℝ≥0) : Lp ℂ 2 (reducedLaw Q) :=
  match ν with
  | .inl i => P t (β i + ζ • a ⟨0, by omega⟩ i)
  | .inr true => transposeEndpoint Q ⟨0, by omega⟩ Pdag β t
  | .inr false => ζ • P t μ

end EinsteinFull
