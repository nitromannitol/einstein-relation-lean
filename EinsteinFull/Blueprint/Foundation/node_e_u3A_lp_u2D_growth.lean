import EinsteinFull.Frozen.ComplexEnvironmentSemigroup
import EinsteinFull.Frozen.ComplexTransposeSemigroup
import EinsteinFull.Frozen.CenteredComplexLp

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Graph node `e:lp-growth`, `paper/main.tex:672–677`.
Each actual forward/transpose operator has its own exponential bound with
factor one. The centered forward family is literally Pi P Pi and satisfies
the semigroup law on centered data. No linear-in-force divergence bound is
used. Constants are chosen before the environment law and complex force. -/
def node_e_u3A_lp_u2D_growthStmt : Prop :=
  ∀ (d : ℕ) (Λ₀ r₀ p : ℝ), 2 ≤ d → 2 ≤ p →
    ∃ C : ℝ, 0 < C ∧
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ)
      (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
    IsComplexEnvironmentSemigroup Q i ζ P → IsComplexTransposeSemigroup Q P T →
    let S := fun (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) =>
      centeredComplexLp Q (P t (centeredComplexLp Q f))
    (∀ (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)),
      MemLp f (ENNReal.ofReal p) (reducedLaw Q) →
        MemLp (P t f) (ENNReal.ofReal p) (reducedLaw Q) ∧
        MemLp (T t f) (ENNReal.ofReal p) (reducedLaw Q) ∧
        MemLp (S t f) (ENNReal.ofReal p) (reducedLaw Q) ∧
        eLpNorm (P t f) (ENNReal.ofReal p) (reducedLaw Q) ≤
          ENNReal.ofReal (Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ))) *
            eLpNorm f (ENNReal.ofReal p) (reducedLaw Q) ∧
        eLpNorm (T t f) (ENNReal.ofReal p) (reducedLaw Q) ≤
          ENNReal.ofReal (Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ))) *
            eLpNorm f (ENNReal.ofReal p) (reducedLaw Q) ∧
        eLpNorm (S t f) (ENNReal.ofReal p) (reducedLaw Q) ≤
          ENNReal.ofReal (2 * Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ))) *
            eLpNorm f (ENNReal.ofReal p) (reducedLaw Q)) ∧
    (letI := reducedLaw_probability Q
     ∀ (t : ℝ≥0) (c : ℂ), P t (Lp.const 2 (reducedLaw Q) c) =
       Lp.const 2 (reducedLaw Q) c) ∧
    (∀ f, S 0 f = centeredComplexLp Q f) ∧
    (∀ s t f, S (s + t) f = S s (S t f))

end EinsteinFull.Blueprint
