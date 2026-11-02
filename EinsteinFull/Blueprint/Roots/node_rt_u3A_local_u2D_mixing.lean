import EinsteinFull.Frozen.RealLocalObservation
import EinsteinFull.Frozen.ComplexEnvironmentSemigroup
import Mathlib.Analysis.SpecialFunctions.Exp

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint

open EinsteinRelation

/-- Exact statement mirror of `rt:local-mixing`; frozen declaration
`EinsteinFull.Frozen.local_mixing`, source `paper/main.tex:415–422`.
No anchor import or conclusion-bearing premise is used. -/
def node_rt_u3A_local_u2D_mixingStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
    ∃ l p c C lam₀ : ℝ,
      0 < l ∧ r₀ < 2 * l ∧ 2 ≤ p ∧ 0 < c ∧ 0 < C ∧
      0 < lam₀ ∧ lam₀ ≤ 1 ∧
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ),
      0 < |lam| → |lam| ≤ lam₀ →
    ∀ P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ (lam : ℂ) P →
    ∀ A : ℝ, l ≤ A → ∀ F G : Lp ℂ 2 (reducedLaw Q),
      IsRealLocalObservation Q (A / |lam|) F →
      IsRealLocalObservation Q (A / |lam|) G →
      MemLp (F : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) →
      MemLp (G : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) →
      (∫ ω, F ω ∂reducedLaw Q) = 0 → ∀ t : ℝ≥0,
      ‖∫ ω, F ω * P t G ω ∂reducedLaw Q‖ ≤
        C * Real.exp (C * A - c * lam ^ 2 * (t : ℝ)) *
          (eLpNorm (F : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal *
          (eLpNorm (G : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal

end EinsteinFull.Blueprint
