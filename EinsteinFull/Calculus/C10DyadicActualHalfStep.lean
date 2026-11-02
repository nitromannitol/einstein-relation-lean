import EinsteinFull.Calculus.C3BootstrapAverageSupport

open EinsteinRelation EinsteinFull MeasureTheory
open scoped NNReal ENNReal Topology

namespace EinsteinFull.Blueprint

/-- The physical half-step estimate at the natural L² exponent. -/
theorem c10_dyadic_actual_half_step (hc : Blueprint.node_e_u3A_centered_u2D_equationsStmt)
    {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β) (ha : IsReducedCoefficientObservation Q a)
    (hμ : IsReducedClockObservation Q μ) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag) (ν : EndpointIndex d)
    (G J : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q))
    (hflux : ∀ t : ℝ≥0, 0 < (t : ℝ) → IsEndpointWeakFlux hd Q ν ζ a
      (indexedEndpoint hd Q ν ζ P Pdag β a μ t) (G t) (J t))
    (s : ℝ) (hs : 0 < s) (t : ℝ) (ht : 0 < t) (H B : ℝ) (hBpos : 0 ≤ B)
    (hH : ‖gaussianAverage hd Q s hs (indexedEndpoint hd Q ν ζ P Pdag β a μ (t/2).toNNReal)‖ ≤ H)
    (hB : ∀ r ∈ Set.Ioo (t/2) t, ‖c3BootstrapFluxVector hd Q ν ζ J s hs t r‖ ≤ B) :
    ‖gaussianAverage hd Q s hs (indexedEndpoint hd Q ν ζ P Pdag β a μ t.toNNReal)‖ ≤
      Real.exp (((endpointDriftSign ν : ℂ) * ζ).im ^ 2 * (t/2) *
        homogenizedCoefficient Q ⟨0, by omega⟩ ⟨0, by omega⟩ / 2) * H + (t/2) * B := by
  have h := c3BootstrapInteraction_half_step hc hd D Q hQ β a μ hβ ha hμ
    ζ P Pdag hP hPdag ν G J hflux s hs t ht 2 le_rfl H B hBpos
    (by simpa using Lp.memLp (gaussianAverage hd Q s hs
      (indexedEndpoint hd Q ν ζ P Pdag β a μ (t/2).toNNReal)))
    (by simpa [← Lp.norm_def] using hH)
    (by intro r hr; simpa using Lp.memLp (c3BootstrapFluxVector hd Q ν ζ J s hs t r))
    (by intro r hr; simpa [← Lp.norm_def] using hB r hr)
  simpa [← Lp.norm_def] using h.2

end EinsteinFull.Blueprint
