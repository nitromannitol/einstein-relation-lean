import EinsteinFull.Frozen.StructuralData
import EinsteinFull.Frozen.SmoothEnvironment
import EinsteinFull.Frozen.ReducedDriftObservation
import EinsteinFull.Frozen.ReducedCoefficientObservation
import EinsteinFull.Frozen.ReducedClockObservation
import EinsteinFull.Frozen.ComplexEnvironmentSemigroup
import EinsteinFull.Frozen.ComplexTransposeSemigroup
import EinsteinFull.Frozen.ComplexHorizontalGradient
import EinsteinFull.Frozen.UncenteredEndpoint
import EinsteinFull.Frozen.ComplexLocalObservation
import EinsteinFull.Frozen.LocalSpatialEnergy
import EinsteinFull.Frozen.CubeIntegralObservation
import EinsteinFull.Frozen.GaussianAverage
import Mathlib.Analysis.Calculus.Deriv.Basic

open MeasureTheory
open scoped NNReal ENNReal
namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Node `p:scalar#unit-initialization`, `paper/main.tex:749–754`.
Bounded-time point and averaged initialization, including time zero and the clock.
The horizon, averaging ratio and moment order may affect the constant; the law,
force, endpoint, time and Gaussian scale may not. -/
def node_p_u3A_scalar_u23_unit_u2D_initializationStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∀ a₀ : ℝ, 0 < a₀ → a₀ < 1 →
    ∀ p : ℝ, 2 ≤ p → ∀ T : ℝ, 1 ≤ T →
    ∃ C : ℝ, 1 ≤ C ∧
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
    ‖ζ‖ ≤ 2 → ∀ t : ℝ≥0, (t : ℝ) ≤ T →
      let U := indexedEndpoint hd Q ν ζ P Pdag β a μ t
      let h : ℝ := 1 / 2 + (d : ℝ) / 4
      (MemLp (U : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧
        (eLpNorm (U : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤ C) ∧
      (∀ s : ℝ, a₀ * (t : ℝ) ≤ s → ∀ hs : 0 < s,
        MemLp (gaussianAverage hd Q s hs U : FieldPair d → ℂ)
          (ENNReal.ofReal p) (reducedLaw Q) ∧
        (eLpNorm (gaussianAverage hd Q s hs U : FieldPair d → ℂ)
          (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
          C * (s ^ (-h) + ‖ζ‖ * s ^ (-(d : ℝ) / 4)))

end EinsteinFull.Blueprint
