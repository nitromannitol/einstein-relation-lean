import EinsteinFull.Frozen.StructuralData
import EinsteinFull.Frozen.SmoothEnvironment
import EinsteinFull.Frozen.ReducedDriftObservation
import EinsteinFull.Frozen.ReducedCoefficientObservation
import EinsteinFull.Frozen.ReducedClockObservation
import EinsteinFull.Frozen.ComplexEnvironmentSemigroup
import EinsteinFull.Frozen.ComplexTransposeSemigroup
import EinsteinFull.Frozen.EndpointWeakFlux
import EinsteinFull.Frozen.GaussianAverage
import EinsteinFull.Frozen.ModelClockEndpoint
import EinsteinFull.Frozen.ModelVelocityEndpoint
import EinsteinFull.Frozen.ModelTransposeEndpoint
import EinsteinFull.Frozen.JointCovariance
import EinsteinFull.Frozen.SchwartzTestNorm
import EinsteinFull.Frozen.VelocityGaussianProfile
import EinsteinFull.Frozen.ClockGaussianProfile
import Mathlib.Analysis.Calculus.Deriv.Basic

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Graph node `e:clock-early`, `paper/main.tex:1205–1210`.
Early unforced centered clock smoothing and its forced homogeneous propagation.
The three propagated errors keep force replacement, early identification and
time replacement distinct; delta=1/4 is the endpoint-comparison split. -/
def node_e_u3A_clock_u2D_earlyStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ gain C t₀ : ℝ, 0 < gain ∧ 0 < C ∧ 1 ≤ t₀ ∧
    ∀ C₀ : ℝ, 0 < C₀ → ∃ Cw T₀ : ℝ, 0 < Cw ∧ 2 ≤ T₀ ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedCoefficientObservation Q a → IsReducedClockObservation Q μ →
    ∀ P : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      (∀ ζ, IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ (P ζ)) →
      let W := fun (ζ : ℂ) (r : ℝ≥0) => centeredComplexLp Q (P ζ r μ)
      let M := centeredComplexLp Q μ
      (∀ (τ : ℝ≥0), t₀ ≤ (τ : ℝ) → ∀ (s : ℝ) (hs : 0 < s),
        2 * (τ : ℝ) ≤ s →
        ‖gaussianAverage hd Q s hs (W 0 τ - M)‖ ≤
          C * s ^ (-(d : ℝ) / 4) * ((τ : ℝ) / s + Real.sqrt ((τ : ℝ) / s))) ∧
      ∀ T : ℝ, T₀ ≤ T → ∀ ζ : ℂ,
        (‖ζ‖ * Real.sqrt T ≤ 2 ∨ ∃ x : ℝ, ζ = (x : ℂ) ∧
          |x| * Real.sqrt T ≤ C₀ * Real.log T ^ (1 / 4 : ℝ)) →
      let τ := T ^ (1 - (1 / 4 : ℝ))
      ∃ hT : 0 < T, ∃ ht : 0 < T - τ,
        t₀ ≤ τ ∧ 2 * τ ≤ T ∧
        ‖ζ • homogeneousAverage Q ⟨0, by omega⟩ (T - τ) ht ζ
            (W ζ τ.toNNReal - W 0 τ.toNNReal)‖ ≤
          Cw * Real.exp (Cw * ‖ζ‖ ^ 2 * T) * T ^ (-(1 / 2 + (d : ℝ) / 4)) *
            Real.sqrt (τ / T) ∧
        ‖ζ • homogeneousAverage Q ⟨0, by omega⟩ (T - τ) ht ζ
            (W 0 τ.toNNReal - M)‖ ≤
          Cw * Real.exp (Cw * ‖ζ‖ ^ 2 * T) * T ^ (-(1 / 2 + (d : ℝ) / 4)) *
            Real.sqrt (τ / T) ∧
        ‖ζ • (homogeneousAverage Q ⟨0, by omega⟩ (T - τ) ht ζ M -
            homogeneousAverage Q ⟨0, by omega⟩ T hT ζ M)‖ ≤
          Cw * Real.exp (Cw * ‖ζ‖ ^ 2 * T) * T ^ (-(1 / 2 + (d : ℝ) / 4)) * (τ / T) ∧
        ‖clockEndpoint Q ζ (P ζ) μ T.toNNReal -
            ζ • homogeneousAverage Q ⟨0, by omega⟩ T hT ζ M‖ ≤
          Cw * Real.exp (Cw * ‖ζ‖ ^ 2 * T) * T ^ (-(1 / 2 + (d : ℝ) / 4) - gain)

end EinsteinFull.Blueprint
