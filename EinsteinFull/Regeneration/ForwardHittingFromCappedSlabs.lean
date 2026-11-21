import EinsteinFull.Regeneration.CappedSlabExitClock
import EinsteinFull.Regeneration.ForwardHittingFromWalk

/-!
# Forward hitting from capped slab comparisons

The actual time-capped slab clock supplies the bounded-time premise in the
biased-walk comparison for the forward hitting estimate.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration Finset
open scoped NNReal ENNReal ProbabilityTheory

namespace EinsteinFull.Regeneration

/-- A biased walk dominated at the actual capped slab exits gives the scaled forward bound. -/
theorem forward_hitting_le_of_capped_slab_walk {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ} (γ : Ω → Path d) (i : Fin d)
    (X : ℕ → Ω → ℝ) (hX : ∀ n, Measurable (X n)) (hind : iIndepFun X μ)
    (hbound : ∀ n, ∀ᵐ ω ∂μ, X n ω ∈ Set.Icc (-1 : ℝ) 1)
    (hmean : ∀ n, (∫ ω, X n ω ∂μ) = (1 / 5 : ℝ))
    (lam L g : ℝ) (hlam : 0 < lam) (hL : (1 / 5 : ℝ) ≤ L) (hg : 0 < g)
    (hcompare : ∀ n, ∀ᵐ ω ∂μ,
      (L / lam) * (∑ j ∈ range n, X j ω) ≤
        γ ω (cappedSlabExitTime (γ ω) i (L / lam) (Real.toNNReal (g / lam ^ 2)) n) i -
          γ ω 0 i)
    (T : ℝ≥0) (a : ℝ) (ha : 0 ≤ a) :
    μ {ω | (T : ℝ≥0∞) ≤ firstHittingAbove (γ ω) i a} ≤
      ENNReal.ofReal (Real.exp (1 / 50) *
        Real.exp (-(1 / (100 * g)) * lam ^ 2 * (T : ℝ) + lam * a)) := by
  let τ : ℕ → Ω → ℝ≥0 := fun n ω =>
    cappedSlabExitTime (γ ω) i (L / lam) (Real.toNNReal (g / lam ^ 2)) n
  have htime (n : ℕ) : ∀ᵐ ω ∂μ, (τ n ω : ℝ) ≤ n * (g / lam ^ 2) := by
    apply Filter.Eventually.of_forall
    intro ω
    have h := cappedSlabExitTime_le (γ ω) i (L / lam) (Real.toNNReal (g / lam ^ 2)) n
    have hh : ((τ n ω : ℝ≥0) : ℝ) ≤ ((n : ℝ≥0) * Real.toNNReal (g / lam ^ 2) : ℝ≥0) :=
      NNReal.coe_le_coe.mpr h
    simpa only [NNReal.coe_mul, NNReal.coe_natCast, Real.coe_toNNReal _ (div_nonneg hg.le (sq_nonneg lam))] using hh
  exact scaled_forward_hitting_le_of_biased_walk μ γ i X hX hind hbound hmean τ
    lam L g hlam hL hg htime hcompare T a ha

end EinsteinFull.Regeneration
