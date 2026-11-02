import EinsteinFull.Calculus.C1ClockAnalyticitySupport
import EinsteinFull.Blueprint.G3.node_stationary_u2D_analytic_u2D_semigroup_u23_clock
import EinsteinFull.Blueprint.Foundation.node_stationary_u2D_analytic_u2D_semigroup
import EinsteinFull.Blueprint.Roots.node_l_u3A_forced_u2D_flux

/-! Partial support only. The exact clock reduction is not established here. -/

open MeasureTheory
open scoped NNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Partial clock contract: shared actual weak-flux witnesses at all positive
 times, with entire L2 dependence of their coordinates. -/
theorem clockL2Witnesses {d : ℕ} (hd : 2 ≤ d) {Λ R : ℝ}
    (Q : EnvironmentLaw d Λ R)
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (ha : IsReducedCoefficientObservation Q a) (μ : Lp ℂ 2 (reducedLaw Q))
    (P : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : ∀ ζ, IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ (P ζ)) :
    ∃ G J : ℂ → ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
      (∀ ζ r, 0 < r →
        IsEndpointWeakFlux hd Q (.inr false) ζ a
          (centeredComplexLp Q (P ζ r μ)) (G ζ r) (J ζ r) ∧
        IsEndpointWeakFlux hd Q (.inr false) ζ a
          (clockEndpoint Q ζ (P ζ) μ r)
          (fun j => ζ • G ζ r j) (fun j => ζ • J ζ r j)) ∧
      ∀ r, 0 < r → ∀ j z,
        AnalyticAt ℂ (fun ζ => G ζ r j) z ∧ AnalyticAt ℂ (fun ζ => J ζ r j) z := by
  refine ⟨ClockAnalyticity.gradient hP μ,
    fun ζ r => ClockAnalyticity.flux Q (ClockAnalyticity.gradient hP μ ζ r), ?_, ?_⟩
  · exact fun ζ r hr => ClockAnalyticity.sharedWeakFlux hd a ha hP μ ζ r hr
  · exact fun r hr j z => ⟨ClockAnalyticity.analyticGradient hP μ r hr j z,
      ClockAnalyticity.analyticFlux hP μ r hr j z⟩

end EinsteinFull.Blueprint
