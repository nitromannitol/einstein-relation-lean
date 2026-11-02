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

/-- Node `e:holder-average`, `paper/main.tex:700–705`.
Gaussian unsmoothing for the actual endpoints, with structural exponent chosen
before the moment order and the actual environment. -/
def node_e_u3A_holder_u2D_averageStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ α : ℝ, 0 < α ∧
    ∀ p : ℝ, 2 ≤ p → ∃ C Cp : ℝ, 1 ≤ C ∧ 0 < Cp ∧
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
    ∀ (t : ℝ≥0), 0 < (t : ℝ) →
      let U := indexedEndpoint hd Q ν ζ P Pdag β a μ t
      let U₈ := indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8)
      MemLp (U₈ : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧
      ∀ b : ℝ, 0 < b → b ≤ 1 / 16 → ∀ hbt : 0 < b * (t : ℝ),
        MemLp ((U - gaussianAverage hd Q (b * (t : ℝ)) hbt U) : FieldPair d → ℂ)
          (ENNReal.ofReal p) (reducedLaw Q) ∧
        (eLpNorm ((U - gaussianAverage hd Q (b * (t : ℝ)) hbt U) : FieldPair d → ℂ)
          (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
          C * b ^ (α / 2) * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ C *
            Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) *
            (eLpNorm (U₈ : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal

end EinsteinFull.Blueprint
