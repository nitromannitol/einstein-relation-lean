import EinsteinFull.Blueprint.Roots.node_p_u3A_tail
import EinsteinFull.Frozen.ComplexTransposeSemigroup
import EinsteinFull.Frozen.EndpointCollection

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Node `p:tail#small-endpoints`, `paper/main.tex:550–556`.
The literal force-time endpoints are centered and small before mixing.
The arbitrary finite p can subsequently be the structural mixing exponent. -/
def node_p_u3A_tail_u23_small_u2D_endpointsStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (p : ℝ), 2 ≤ p → ∃ C : ℝ, 0 < C ∧
  ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (μ : Lp ℂ 2 (reducedLaw Q)),
    IsReducedDriftObservation Q hQ β →
    IsReducedCoefficientObservation Q a → IsReducedClockObservation Q μ →
    ∀ lam : ℝ, 0 < |lam| → |lam| ≤ Real.exp (-1) →
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
    IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ (lam : ℂ) P →
    IsComplexTransposeSemigroup Q P Pdag →
    let s := |lam|
    let T : ℝ≥0 := ((s ^ 2)⁻¹).toNNReal
    let h : ℝ := 1 + (d : ℝ) / 2
    let F := transposeEndpoint Q ⟨0, by omega⟩ Pdag β T
    ∀ (j : Fin d) (velocity : Bool),
    let G := if velocity then velocityEndpoint Q ⟨0, by omega⟩ j (lam : ℂ) P β a T
      else clockEndpoint Q (lam : ℂ) P μ T
    MemLp (F : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧
    MemLp (G : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧
    (∫ ω, F ω ∂reducedLaw Q) = 0 ∧
    (∫ ω, G ω ∂reducedLaw Q) = 0 ∧
    (eLpNorm (F : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal +
      (eLpNorm (G : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        C * s ^ h ∧
    ∀ t : ℝ≥0, 2 * (T : ℝ) ≤ (t : ℝ) →
      (if velocity then velocityCorrelation Q ⟨0, by omega⟩ j (lam : ℂ) P β a t
       else clockCorrelation Q ⟨0, by omega⟩ (lam : ℂ) P β μ t) =
        ∫ ω, F ω * P (t - 2 * T) G ω ∂reducedLaw Q

end EinsteinFull.Blueprint
