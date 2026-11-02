import EinsteinFull.Blueprint.Roots.node_p_u3A_tail
import EinsteinFull.Frozen.ComplexTransposeSemigroup
import EinsteinFull.Frozen.EndpointCollection
import EinsteinFull.Frozen.RealLocalObservation
import EinsteinRelation.Probability.LocalSigma
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semiring

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Node `p:tail#annuli`, `paper/main.tex:558–569`.
Actual conditional expectations of either force-time endpoint over the joint
fields. The weight is fixed before the constants; the polynomial locality
loss enters the structural logarithmic cutoff, never the endpoint power. -/
def node_p_u3A_tail_u23_annuliStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ l₀ c : ℝ, ∃ N : ℕ,
    0 < l₀ ∧ D.dependenceRange < 2 * l₀ ∧ 0 < c ∧
    ∀ (l p weight : ℝ), l₀ ≤ l → 2 ≤ p → 0 ≤ weight →
    ∃ C C₁ C₂ : ℝ, 0 < C ∧ 0 < C₁ ∧ 0 < C₂ ∧
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
    let E := fun (U : Lp ℂ 2 (reducedLaw Q)) (n : ℕ) =>
      (condExpL2 ℂ ℂ (Probability.localSigma_le_borel
        {x : Vec d | euclideanNorm x < (n : ℝ) * l / s}) U : Lp ℂ 2 (reducedLaw Q))
    let Δ := fun (U : Lp ℂ 2 (reducedLaw Q)) (n : ℕ) =>
      if n = 1 then E U 1 else E U n - E U (n - 1)
    let normp := fun U : Lp ℂ 2 (reducedLaw Q) =>
      (eLpNorm (U : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal
    let cutoff : ℕ := ⌈C₁ + C₂ * Real.sqrt (Real.log (1 / s))⌉₊
    ∀ U ∈ ({F, G} : Set (Lp ℂ 2 (reducedLaw Q))),
      (∀ n : ℕ, 1 ≤ n →
        ∃ V : Lp ℂ 2 (reducedLaw Q),
          IsRealLocalObservation Q ((n : ℝ) * l / (2 * s)) V ∧
          (∀ᵐ ω ∂reducedLaw Q,
            ‖U ω - V ω‖ ≤ C * s ^ (-(N : ℝ)) * Real.exp (-c * (n : ℝ) ^ 2))) ∧
      (∀ n : ℕ, 1 ≤ n →
        IsRealLocalObservation Q ((n : ℝ) * l / s) (Δ U n) ∧
        MemLp (Δ U n : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧
        (∫ ω, Δ U n ω ∂reducedLaw Q) = 0 ∧
        normp (Δ U n) ≤ C * min (s ^ h)
          (s ^ (-(N : ℝ)) * Real.exp (-c * ((n : ℝ) - 1) ^ 2))) ∧
      Summable (fun k : ℕ => Real.exp (weight * (k + 1 : ℕ)) * normp (Δ U (k + 1))) ∧
      (∑' k : ℕ, Real.exp (weight * (k + 1 : ℕ)) * normp (Δ U (k + 1))) ≤
        C * s ^ h * Real.exp (C * Real.sqrt (Real.log (1 / s))) ∧
      (∑' k : ℕ, if cutoff < k + 1 then
        Real.exp (weight * (k + 1 : ℕ)) * normp (Δ U (k + 1)) else 0) ≤
        C * s ^ (h + 1)

end EinsteinFull.Blueprint
