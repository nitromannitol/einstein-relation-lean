import EinsteinFull.Frozen.EndpointCollection

open MeasureTheory
open scoped NNReal

namespace EinsteinFull
open EinsteinRelation

/-- The literal sum of the d+2 scalar endpoint Lp norms, p finite.
Source bounds using this expression also assert MemLp, so toReal cannot discard infinity. -/
noncomputable def endpointMomentSum {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (p : ℝ) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (t : ℝ≥0) : ℝ :=
  (eLpNorm (transposeEndpoint Q ⟨0, by omega⟩ Pdag β t : FieldPair d → ℂ)
    (ENNReal.ofReal p) (reducedLaw Q)).toReal +
  (∑ i : Fin d, (eLpNorm (velocityEndpoint Q ⟨0, by omega⟩ i ζ P β a t : FieldPair d → ℂ)
    (ENNReal.ofReal p) (reducedLaw Q)).toReal) +
  (eLpNorm (clockEndpoint Q ζ P μ t : FieldPair d → ℂ)
    (ENNReal.ofReal p) (reducedLaw Q)).toReal

end EinsteinFull
