import EinsteinFull.Blueprint.Roots.node_p_u3A_response
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Analytic.Basic

open MeasureTheory Filter
open scoped Topology NNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Graph node `p:response#cesaro-abel`, `paper/main.tex:282–282`.
At each nonzero signed force, actual velocity and clock witnesses precede
time and Laplace limits. Both Cesaro expectation limits and Abel expectation
limits are asserted; clock bounds retain arbitrary actual density bounds. -/
def node_p_u3A_response_u23_cesaro_u2D_abelStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (μ : Lp ℂ 2 (reducedLaw Q)),
    IsReducedDriftObservation Q hQ β →
    IsReducedCoefficientObservation Q a → IsReducedClockObservation Q μ →
    ∀ (lam : ℝ), lam ≠ 0 →
    ∀ (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
    IsComplexEnvironmentSemigroup Q (⟨0, by omega⟩ : Fin d) (lam : ℂ) P →
    ∀ Y : QuenchedPathLaws d,
    (∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator (⟨0, by omega⟩ : Fin d) ω lam)
        0 (Y (0, ω))) →
    ∃ (velocity : Vec d) (η : ℝ),
      HasQuenchedVelocity Q.measure (originLaw Y) velocity ∧
      HasReducedClockRate Q Y η ∧
      (∀ i : Fin d,
        Tendsto (fun T : ℝ => (T : ℂ)⁻¹ *
          ∫ t in (0 : ℝ)..T, ∫ ω,
            (P t.toNNReal (β i + (lam : ℂ) • a (⟨0, by omega⟩ : Fin d) i)) ω
              ∂reducedLaw Q) atTop (𝓝 (velocity i : ℂ)) ∧
        Tendsto (fun s : ℝ => (s : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
          (Real.exp (-s * t) : ℂ) * (∫ ω,
            (P t.toNNReal (β i + (lam : ℂ) • a (⟨0, by omega⟩ : Fin d) i)) ω
              ∂reducedLaw Q)) (𝓝[>] (0 : ℝ)) (𝓝 (velocity i : ℂ))) ∧
      Tendsto (fun T : ℝ => (T : ℂ)⁻¹ *
        ∫ t in (0 : ℝ)..T, ∫ ω, (P t.toNNReal μ) ω ∂reducedLaw Q)
          atTop (𝓝 (η : ℂ)) ∧
      Tendsto (fun s : ℝ => (s : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
        (Real.exp (-s * t) : ℂ) * (∫ ω, (P t.toNNReal μ) ω ∂reducedLaw Q))
          (𝓝[>] (0 : ℝ)) (𝓝 (η : ℂ)) ∧
      ∀ lower upper : ℝ,
        (∀ᵐ ω ∂reducedLaw Q, ∀ x : Vec d,
          lower ≤ ω.2 x ∧ ω.2 x ≤ upper) →
        (∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂originLaw Y ω, ∀ t : ℝ≥0,
          lower * (t : ℝ) ≤ (Clock.physicalPathClock ω γ t : ℝ) ∧
          (Clock.physicalPathClock ω γ t : ℝ) ≤ upper * (t : ℝ)) ∧
        lower ≤ η ∧ η ≤ upper

end EinsteinFull.Blueprint
