import EinsteinFull.Blueprint.Roots.node_p_u3A_response
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Analytic.Basic

open MeasureTheory Filter
open scoped Topology NNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Graph node `finite-time-analyticity#abel-removal`, `paper/main.tex:578`.
At fixed small signed real force, integrability and both undamped limits
are conclusions. No Abel-removal premise enters the analytic construction. -/
def node_finite_u2D_time_u2D_analyticity_u23_abel_u2D_removalStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ lamStar : ℝ, 0 < lamStar ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (μ : Lp ℂ 2 (reducedLaw Q)),
    IsReducedDriftObservation Q hQ β →
    IsReducedCoefficientObservation Q a → IsReducedClockObservation Q μ →
    ∀ P : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
    (∀ ζ : ℂ, IsComplexEnvironmentSemigroup Q (⟨0, by omega⟩ : Fin d) ζ (P ζ)) →
    ∀ lam : ℝ, lam ≠ 0 → |lam| ≤ lamStar →
    let ζ : ℂ := lam
    (∀ i : Fin d,
      Integrable (fun t : ℝ => velocityCorrelation Q (⟨0, by omega⟩ : Fin d) i ζ (P ζ) β a t.toNNReal)
        (volume.restrict (Set.Ioi 0)) ∧
      Tendsto (fun s : ℝ => ∫ t in Set.Ioi (0 : ℝ),
        (Real.exp (-s * t) : ℂ) * velocityCorrelation Q (⟨0, by omega⟩ : Fin d) i ζ (P ζ) β a t.toNNReal)
        (𝓝[>] (0 : ℝ))
        (𝓝 (∫ t in Set.Ioi (0 : ℝ), velocityCorrelation Q (⟨0, by omega⟩ : Fin d) i ζ (P ζ) β a t.toNNReal))) ∧
    Integrable (fun t : ℝ => clockCorrelation Q (⟨0, by omega⟩ : Fin d) ζ (P ζ) β μ t.toNNReal)
      (volume.restrict (Set.Ioi 0)) ∧
    Tendsto (fun s : ℝ => ∫ t in Set.Ioi (0 : ℝ),
      (Real.exp (-s * t) : ℂ) * clockCorrelation Q (⟨0, by omega⟩ : Fin d) ζ (P ζ) β μ t.toNNReal)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ t in Set.Ioi (0 : ℝ), clockCorrelation Q (⟨0, by omega⟩ : Fin d) ζ (P ζ) β μ t.toNNReal))

end EinsteinFull.Blueprint
