import EinsteinFull.Blueprint.Roots.node_p_u3A_response
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Analytic.Basic

open MeasureTheory Filter
open scoped Topology NNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Graph node `p:response#core-extension`, `paper/main.tex:281–282`.
The actual generator identity extends to every bounded local datum without
extra regularity. The derivative is at positive time and the Laplace identity
has the source normalization. -/
def node_p_u3A_response_u23_core_u2D_extensionStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (μ : Lp ℂ 2 (reducedLaw Q)),
    IsReducedDriftObservation Q hQ β →
    IsReducedCoefficientObservation Q a → IsReducedClockObservation Q μ →
    ∀ (lam : ℝ)
      (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
    IsComplexEnvironmentSemigroup Q (⟨0, by omega⟩ : Fin d) (lam : ℂ) P →
    ∀ F : Lp ℂ 2 (reducedLaw Q), IsBoundedLocalObservation Q F →
    (∀ t : ℝ, 0 < t →
      HasDerivAt (fun u : ℝ => ∫ ω, (P u.toNNReal F) ω ∂reducedLaw Q)
        (-(2 * lam : ℂ) * (∫ ω, β (⟨0, by omega⟩ : Fin d) ω *
          (P t.toNNReal F) ω ∂reducedLaw Q)) t) ∧
    ∀ s : ℝ, 0 < s →
      (s : ℂ) * (∫ t in Set.Ioi (0 : ℝ),
        (Real.exp (-s * t) : ℂ) * (∫ ω, (P t.toNNReal F) ω ∂reducedLaw Q)) =
      (∫ ω, F ω ∂reducedLaw Q) - (2 * lam : ℂ) *
        (∫ t in Set.Ioi (0 : ℝ), (Real.exp (-s * t) : ℂ) *
          (∫ ω, β (⟨0, by omega⟩ : Fin d) ω *
            (P t.toNNReal F) ω ∂reducedLaw Q))

end EinsteinFull.Blueprint
