import EinsteinFull.Frozen.StructuralData
import EinsteinFull.Frozen.SmoothEnvironment
import EinsteinFull.Frozen.ReducedDriftObservation
import EinsteinFull.Frozen.ReducedCoefficientObservation
import EinsteinFull.Frozen.ReducedClockObservation
import EinsteinFull.Frozen.ComplexEnvironmentSemigroup
import EinsteinFull.Frozen.ComplexTransposeSemigroup
import EinsteinFull.Frozen.GaussianAverage

import EinsteinFull.Frozen.IndexedEndpoint

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Node `p:scalar#smoothing-selection`, `paper/main.tex:770–774`.
SCALAR-SCOPE-1: choose one outer fraction before p, then an inner fraction,
growth weight and starting threshold after p. The normalized unsmoothing
error is at most half the preceding point bound. All data and operators below
are the actual reduced observations and semigroups. -/
def node_p_u3A_scalar_u23_smoothing_u2D_selectionStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ a₀ : ℝ, 0 < a₀ ∧ a₀ ≤ 1 / 16 ∧
    ∀ p : ℝ, 2 ≤ p → ∃ b growth T₀ : ℝ,
      0 < b ∧ b ≤ a₀ ∧ 0 < growth ∧ 16 ≤ T₀ ∧ b⁻¹ ≤ T₀ ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
      (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
      let U := fun t => indexedEndpoint hd Q ν ζ P Pdag β a μ t
      let h : ℝ := 1 / 2 + (d : ℝ) / 4
      let w := fun s : ℝ => s ^ (-h) + ‖ζ‖ * s ^ (-(d : ℝ) / 4)
      let N := fun f : Lp ℂ 2 (reducedLaw Q) =>
        (eLpNorm (f : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal
      ∀ t : ℝ≥0, T₀ ≤ (t : ℝ) → ∀ Kprime : ℝ, 1 ≤ Kprime →
          MemLp (U (t / 8) : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) →
          N (U (t / 8)) ≤
            Kprime * Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 8) * w ((t : ℝ) / 8) →
          ∀ hbt : 0 < b * (t : ℝ),
            MemLp ((U t - gaussianAverage hd Q (b * (t : ℝ)) hbt (U t)) :
              FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧
            N (U t - gaussianAverage hd Q (b * (t : ℝ)) hbt (U t)) ≤
              (Kprime / 2) * Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ)) * w (t : ℝ) ∧
            (∀ Kavg : ℝ, 1 ≤ Kavg →
              MemLp (gaussianAverage hd Q (b * (t : ℝ)) hbt (U t) :
                FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) →
              N (gaussianAverage hd Q (b * (t : ℝ)) hbt (U t)) ≤
                Kavg * Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ)) * w (b * (t : ℝ)) →
              MemLp (U t : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧
              N (U t) ≤ (b ^ (-h) * Kavg + Kprime / 2) *
                Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ)) * w (t : ℝ))

end EinsteinFull.Blueprint
