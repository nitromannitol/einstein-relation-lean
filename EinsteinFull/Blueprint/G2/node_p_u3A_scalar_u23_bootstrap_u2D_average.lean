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

/-- Node `p:scalar#bootstrap-average`, `paper/main.tex:756–768`.
The actual endpoint bootstrap has coefficient one on its preceding averaged
bound. The terminal window is imposed only at F, and the last step is truncated
at F. The inner averaging fraction may be selected after the moment order.
The structural gain and force-window exponents precede both choices. -/
def node_p_u3A_scalar_u23_bootstrap_u2D_averageStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ ε η₀ : ℝ, 0 < ε ∧ 0 < η₀ ∧ η₀ < 1 / 2 ∧
    ∀ b : ℝ, 0 < b → b ≤ 1 / 16 →
    ∀ p : ℝ, 2 ≤ p → ∃ C growth₀ T₀ : ℝ,
      0 < C ∧ 0 < growth₀ ∧ 16 ≤ T₀ ∧ b⁻¹ ≤ T₀ ∧
    ∀ growth : ℝ, growth₀ ≤ growth →
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
      let Avg := fun (S K : ℝ) => ∀ r : ℝ≥0, 1 ≤ (r : ℝ) → (r : ℝ) ≤ S →
        ∀ s : ℝ, b * (r : ℝ) ≤ s → ∀ hs : 0 < s,
          MemLp (gaussianAverage hd Q s hs (U r) : FieldPair d → ℂ)
            (ENNReal.ofReal p) (reducedLaw Q) ∧
          N (gaussianAverage hd Q s hs (U r)) ≤
            K * Real.exp (growth * ‖ζ‖ ^ 2 * (r : ℝ)) * w s
      let Point := fun (S K : ℝ) => ∀ r : ℝ≥0, 1 ≤ (r : ℝ) → (r : ℝ) ≤ S →
        MemLp (U r : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧
        N (U r) ≤ K * Real.exp (growth * ‖ζ‖ ^ 2 * (r : ℝ)) * w (r : ℝ)
      ‖ζ‖ ≤ 1 → ∀ F T : ℝ, T₀ ≤ T → T ≤ F →
        ‖ζ‖ * Real.sqrt F ≤ F ^ η₀ →
        ∀ K Kprime : ℝ, 1 ≤ K → 1 ≤ Kprime →
          Avg T K → Point T Kprime →
          Avg (min (2 * T) F) (K + C * T ^ (-ε) * Kprime)

end EinsteinFull.Blueprint
