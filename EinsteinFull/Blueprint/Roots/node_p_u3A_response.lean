import EinsteinFull.Frozen.SmoothEnvironment
import EinsteinFull.Frozen.ComplexEnvironmentSemigroup
import EinsteinFull.Frozen.ReducedCoefficientObservation
import EinsteinFull.Frozen.ReducedDriftObservation
import EinsteinFull.Frozen.ReducedClockObservation
import EinsteinFull.Frozen.VelocityCorrelation
import EinsteinFull.Frozen.ClockCorrelation
import EinsteinFull.Frozen.BoundedLocalObservation
import EinsteinFull.Frozen.ReducedClockRate
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

open MeasureTheory Filter
open scoped Topology NNReal

namespace EinsteinFull.Blueprint

open EinsteinRelation

/-- Exact statement mirror of `p:response`; frozen declaration
`EinsteinFull.Frozen.response`, source `paper/main.tex:263–279`.
No anchor import or conclusion-bearing premise is used. -/
def node_p_u3A_responseStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (μ : Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β)
    (ha : IsReducedCoefficientObservation Q a)
    (hμ : IsReducedClockObservation Q μ)
    (lam : ℝ)
    (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q (⟨0, by omega⟩ : Fin d) (lam : ℂ) P),
    (∀ F : Lp ℂ 2 (reducedLaw Q), IsBoundedLocalObservation Q F →
      ∀ s : ℝ, 0 < s →
        (s : ℂ) * (∫ t in Set.Ioi (0 : ℝ),
          (Real.exp (-s * t) : ℂ) * (∫ ω, (P t.toNNReal F) ω ∂reducedLaw Q)) =
        (∫ ω, F ω ∂reducedLaw Q) - (2 * lam : ℂ) *
          (∫ t in Set.Ioi (0 : ℝ), (Real.exp (-s * t) : ℂ) *
            (∫ ω, β (⟨0, by omega⟩ : Fin d) ω *
              (P t.toNNReal F) ω ∂reducedLaw Q))) ∧
    (lam ≠ 0 → ∀ (Y : QuenchedPathLaws d),
      (∀ᵐ ω ∂Q.measure,
        SolvesMartingaleProblem
          (reducedGenerator (⟨0, by omega⟩ : Fin d) ω lam) 0 (Y (0, ω))) →
      ∀ (velocity : Vec d), HasQuenchedVelocity Q.measure (originLaw Y) velocity →
      ∀ (η : ℝ), HasReducedClockRate Q Y η →
      ∃ (k : Fin d → ℝ) (j : ℝ),
        (∀ i : Fin d, Tendsto (fun s : ℝ => ∫ t in Set.Ioi (0 : ℝ),
          (Real.exp (-s * t) : ℂ) *
            velocityCorrelation Q (⟨0, by omega⟩ : Fin d) i
              (lam : ℂ) P β a t.toNNReal)
          (𝓝[>] (0 : ℝ)) (𝓝 (k i : ℂ))) ∧
        Tendsto (fun s : ℝ => ∫ t in Set.Ioi (0 : ℝ), (Real.exp (-s * t) : ℂ) *
          clockCorrelation Q (⟨0, by omega⟩ : Fin d)
            (lam : ℂ) P β μ t.toNNReal)
          (𝓝[>] (0 : ℝ)) (𝓝 (j : ℂ)) ∧
        (∀ i : Fin d, velocity i =
          lam * (∫ ω, (a (⟨0, by omega⟩ : Fin d) i ω).re ∂reducedLaw Q) -
            2 * lam * k i) ∧
        η = (∫ ω, (μ ω).re ∂reducedLaw Q) - 2 * j ∧
        ∀ lower upper : ℝ,
          (∀ᵐ ω ∂reducedLaw Q, ∀ x : Vec d,
            lower ≤ ω.2 x ∧ ω.2 x ≤ upper) → lower ≤ η ∧ η ≤ upper)

end EinsteinFull.Blueprint
