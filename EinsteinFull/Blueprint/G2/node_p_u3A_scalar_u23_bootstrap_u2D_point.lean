import EinsteinFull.Frozen.StructuralData
import EinsteinFull.Frozen.SmoothEnvironment
import EinsteinFull.Frozen.ReducedDriftObservation
import EinsteinFull.Frozen.ReducedCoefficientObservation
import EinsteinFull.Frozen.ReducedClockObservation
import EinsteinFull.Frozen.ComplexEnvironmentSemigroup
import EinsteinFull.Frozen.ComplexTransposeSemigroup
import EinsteinFull.Frozen.EndpointCollection
import EinsteinFull.Frozen.GaussianDerivativeAverage

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint

open EinsteinRelation

/-- Node `p:scalar#bootstrap-point`, `paper/main.tex:770–774`.
Consumer-facing closure of the coupled averaged/point bootstrap: the uniform
wide-window and bounded-disc estimates, including every fixed Gaussian
kernel derivative. The structural outer fraction and window exponent precede p.
The inner fraction, half-error absorption, ratio invariant and summable dyadic
product belong to the proof of this closure, not to additional premises. -/
def node_p_u3A_scalar_u23_bootstrap_u2D_pointStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ a₀ η₀ : ℝ, 0 < a₀ ∧ a₀ < 1 ∧ 0 < η₀ ∧
    ∀ p : ℝ, 2 ≤ p → ∃ C Dp t₀ : ℝ, ∃ Cder : ℕ → ℝ,
      0 < C ∧ 0 < Dp ∧ 1 ≤ t₀ ∧ (∀ k, 0 < Cder k) ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
      (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag →
      let h : ℝ := 1 / 2 + (d : ℝ) / 4
      (∀ t : ℝ≥0, 1 ≤ (t : ℝ) → ‖ζ‖ * Real.sqrt (t : ℝ) ≤ 2 →
        (∀ U ∈ endpointCollection Q ⟨0, by omega⟩ ζ P Pdag β a μ t,
          MemLp (U : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)) ∧
        (eLpNorm (transposeEndpoint Q ⟨0, by omega⟩ Pdag β t : FieldPair d → ℂ)
          (ENNReal.ofReal p) (reducedLaw Q)).toReal +
        (∑ j : Fin d, (eLpNorm
          (velocityEndpoint Q ⟨0, by omega⟩ j ζ P β a t : FieldPair d → ℂ)
          (ENNReal.ofReal p) (reducedLaw Q)).toReal) +
        (eLpNorm (clockEndpoint Q ζ P μ t : FieldPair d → ℂ)
          (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤ C * (t : ℝ) ^ (-h)) ∧
      (∀ t : ℝ≥0, t₀ ≤ (t : ℝ) → ‖ζ‖ ≤ 1 →
        ‖ζ‖ * Real.sqrt (t : ℝ) ≤ (t : ℝ) ^ η₀ →
        ∀ U ∈ endpointCollection Q ⟨0, by omega⟩ ζ P Pdag β a μ t,
        (MemLp (U : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧
          (eLpNorm (U : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
          C * Real.exp (Dp * ‖ζ‖ ^ 2 * (t : ℝ)) *
            ((t : ℝ) ^ (-h) + ‖ζ‖ * (t : ℝ) ^ (-(d : ℝ) / 4))) ∧
        (∀ s : ℝ, a₀ * (t : ℝ) ≤ s → ∀ hs : 0 < s,
          MemLp (gaussianAverage hd Q s hs U : FieldPair d → ℂ)
            (ENNReal.ofReal p) (reducedLaw Q) ∧
          (eLpNorm (gaussianAverage hd Q s hs U : FieldPair d → ℂ)
            (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
            C * Real.exp (Dp * ‖ζ‖ ^ 2 * (t : ℝ)) *
              (s ^ (-h) + ‖ζ‖ * s ^ (-(d : ℝ) / 4))) ∧
        (∀ (k : ℕ) (dirs : Fin k → Fin d) (s : ℝ),
          2 * a₀ * (t : ℝ) ≤ s → ∀ hs : 0 < s,
          MemLp (gaussianDerivativeAverage hd Q s hs k dirs U : FieldPair d → ℂ)
            (ENNReal.ofReal p) (reducedLaw Q) ∧
          (eLpNorm (gaussianDerivativeAverage hd Q s hs k dirs U : FieldPair d → ℂ)
            (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
            Cder k * Real.exp (Dp * ‖ζ‖ ^ 2 * (t : ℝ)) *
              s ^ (-(k : ℝ) / 2) *
                (s ^ (-h) + ‖ζ‖ * s ^ (-(d : ℝ) / 4))))

end EinsteinFull.Blueprint
