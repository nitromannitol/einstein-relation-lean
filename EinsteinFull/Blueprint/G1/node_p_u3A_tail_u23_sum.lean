import EinsteinFull.Blueprint.G1.node_p_u3A_tail_u23_annuli

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Node `p:tail#sum`, `paper/main.tex:570–575`.
The double series is formed from the literal conditional annuli, is absolutely
summable and equals the original signed-force correlation. All mixing and
tail constants precede the actual law, endpoints and semigroups. -/
def node_p_u3A_tail_u23_sumStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ l p C c C_T lam₀ : ℝ,
    0 < l ∧ D.dependenceRange < 2 * l ∧ 2 ≤ p ∧
    0 < C ∧ 0 < c ∧ 2 ≤ C_T ∧
    0 < lam₀ ∧ lam₀ ≤ Real.exp (-1) ∧
  ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (μ : Lp ℂ 2 (reducedLaw Q)),
    IsReducedDriftObservation Q hQ β →
    IsReducedCoefficientObservation Q a → IsReducedClockObservation Q μ →
    ∀ lam : ℝ, 0 < |lam| → |lam| ≤ lam₀ →
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
    ∀ t : ℝ≥0, C_T / s ^ 2 ≤ (t : ℝ) →
    let pair := fun k : ℕ × ℕ =>
      ∫ ω, Δ F (k.1 + 1) ω * P (t - 2 * T) (Δ G (k.2 + 1)) ω ∂reducedLaw Q
    let K := if velocity then velocityCorrelation Q ⟨0, by omega⟩ j (lam : ℂ) P β a t
      else clockCorrelation Q ⟨0, by omega⟩ (lam : ℂ) P β μ t
    (∀ n m : ℕ,
      ‖pair (n, m)‖ ≤
        C * Real.exp (C * ((n + 1 : ℕ) + (m + 1 : ℕ)) -
          c * s ^ 2 * ((t : ℝ) - 2 * (T : ℝ))) *
          normp (Δ F (n + 1)) * normp (Δ G (m + 1))) ∧
    Summable (fun k => ‖pair k‖) ∧
    HasSum pair K ∧
    (∑' k, ‖pair k‖) ≤
      C * s ^ (2 * h) * Real.exp (C * Real.sqrt (Real.log (1 / s)) -
        c * s ^ 2 * ((t : ℝ) - 2 * (T : ℝ))) ∧
    2 * h = (d : ℝ) + 2 ∧ s ^ 2 * (T : ℝ) = 1 ∧
    ‖K‖ ≤ C * s ^ (d + 2) *
      Real.exp (C * Real.sqrt (Real.log (1 / s)) - c * lam ^ 2 * (t : ℝ))

end EinsteinFull.Blueprint
