import EinsteinFull.Blueprint.Foundation.node_e_u3A_forced_u2D_locality

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Pending internal revision of `e:forced-locality`, paper/main.tex:715,754.
Retains V1 and adds only the bounded-force short-time scalar localization
needed by the endpoint consumer. The fixed lower radius follows the bounded-time
comparison in line 715; no small-radius gradient estimate is asserted.
Constants may depend on the force-disc bound, but precede the law and time.
This draft requires the next Foundation Prop review before adoption. -/
def node_e_u3A_forced_u2D_localityStmtV2 : Prop :=
  node_e_u3A_forced_u2D_localityStmt ∧
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (B : ℝ), 0 < B →
    ∃ C c : ℝ, 1 ≤ C ∧ 0 < c ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
      (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ, ‖ζ‖ ≤ B →
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
    ∀ t : ℝ≥0, 0 < (t : ℝ) → (t : ℝ) < 1 →
    ∀ ρ : ℝ, C ≤ ρ →
      ∃ Uloc : Lp ℂ 2 (reducedLaw Q),
        IsComplexLocalObservation Q ρ Uloc ∧
        ∀ᵐ ω ∂reducedLaw Q,
          ‖uncenteredEndpoint hd Q ν ζ P Pdag β a μ t ω - Uloc ω‖ ≤
            C * Real.exp (-c * ρ ^ 2 / (t : ℝ))

/-- The pending short-time revision preserves every V1 conclusion. -/
theorem forcedLocalityV1_of_v2 (h : node_e_u3A_forced_u2D_localityStmtV2) :
    node_e_u3A_forced_u2D_localityStmt := h.1

end EinsteinFull.Blueprint
