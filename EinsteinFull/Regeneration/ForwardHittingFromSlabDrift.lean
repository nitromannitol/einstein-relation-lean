import EinsteinFull.Regeneration.ForwardHittingFromBoundedSlabs
import EinsteinFull.Regeneration.AdaptedConditionalDrift

/-!
# Forward hitting from conditional slab drift

Positive conditional drift for the actual capped slab increments implies the
scaled forward-hitting estimate.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration Finset
open scoped NNReal ENNReal ProbabilityTheory

namespace EinsteinFull.Regeneration

/-- Positive conditional drift of the actual capped increments implies the scaled
forward-hitting estimate. -/
theorem forward_hitting_le_of_capped_slab_conditional_drift {Ω : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d : ℕ} (γ : Ω → Path d) (i : Fin d) (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)
    (lam L g : ℝ) (hlam : 0 < lam) (hL : (1 / 20 : ℝ) ≤ L) (hg : 0 < g)
    (hadapt : StronglyAdapted ℱ (fun j ω =>
      cappedSlabIncrement (γ ω) i (L / lam) (Real.toNNReal (g / lam ^ 2)) j))
    (hmean0 : (1 / 5 : ℝ) ≤ ∫ ω,
      cappedSlabIncrement (γ ω) i (L / lam) (Real.toNNReal (g / lam ^ 2)) 0 ∂μ)
    (hdrift : ∀ j, ∀ᵐ ω ∂μ, (1 / 5 : ℝ) ≤
      μ[fun ω => cappedSlabIncrement (γ ω) i (L / lam)
        (Real.toNNReal (g / lam ^ 2)) (j + 1) | ℱ j] ω)
    (T : ℝ≥0) (a : ℝ) (ha : 0 ≤ a) :
    μ {ω | (T : ℝ≥0∞) ≤ firstHittingAbove (γ ω) i a} ≤
      ENNReal.ofReal (Real.exp (1 / 200) *
        Real.exp (-(1 / (400 * g)) * lam ^ 2 * (T : ℝ) + lam * a)) := by
  let X : ℕ → Ω → ℝ := fun j ω =>
    cappedSlabIncrement (γ ω) i (L / lam) (Real.toNNReal (g / lam ^ 2)) j
  let τ : ℕ → Ω → ℝ≥0 := fun n ω =>
    cappedSlabExitTime (γ ω) i (L / lam) (Real.toNNReal (g / lam ^ 2)) n
  have hLpos : 0 < L := by linarith
  have htime (n : ℕ) : ∀ᵐ ω ∂μ, (τ n ω : ℝ) ≤ n * (g / lam ^ 2) := by
    apply Filter.Eventually.of_forall
    intro ω
    have h := cappedSlabExitTime_le (γ ω) i (L / lam) (Real.toNNReal (g / lam ^ 2)) n
    have hh : ((τ n ω : ℝ≥0) : ℝ) ≤ ((n : ℝ≥0) * Real.toNNReal (g / lam ^ 2) : ℝ≥0) :=
      NNReal.coe_le_coe.mpr h
    simpa only [NNReal.coe_mul, NNReal.coe_natCast, Real.coe_toNNReal _ (div_nonneg hg.le (sq_nonneg lam))] using hh
  have hcompare (n : ℕ) : ∀ᵐ ω ∂μ,
      (L / lam) * (∑ j ∈ range n, X j ω) ≤ γ ω (τ n ω) i - γ ω 0 i := by
    apply Filter.Eventually.of_forall
    intro ω
    exact (sum_cappedSlabIncrement (γ ω) i (L / lam) (div_pos hLpos hlam)
      (Real.toNNReal (g / lam ^ 2)) n).le
  have hbound (j : ℕ) : ∀ᵐ ω ∂μ, X j ω ∈ Set.Icc (-1 : ℝ) 1 :=
    Filter.Eventually.of_forall (fun ω => cappedSlabIncrement_mem_Icc (γ ω) i (L / lam)
      (div_pos hLpos hlam) (Real.toNNReal (g / lam ^ 2)) j)
  have htail := adapted_walk_lower_tail_of_conditional_drift μ ℱ X hadapt hbound hmean0 hdrift
  have hraw := forward_hitting_le_of_weaker_lower_tails μ γ i X htail τ
    (L / lam) (g / lam ^ 2) (div_pos hLpos hlam) (div_pos hg (sq_pos_of_pos hlam))
    htime hcompare T a ha
  have hspace : (a / (L / lam)) / 20 = (lam * a) / (20 * L) := by field_simp
  have hspace_le : (lam * a) / (20 * L) ≤ lam * a := by
    apply (div_le_iff₀ (by positivity : 0 < 20 * L)).2
    nlinarith [mul_nonneg hlam.le ha]
  have htime_eq : (T : ℝ) / (400 * (g / lam ^ 2)) =
      (1 / (400 * g)) * lam ^ 2 * (T : ℝ) := by field_simp
  have harg : (a / (L / lam)) / 20 + 1 / 200 - (T : ℝ) / (400 * (g / lam ^ 2)) ≤
      1 / 200 + (-(1 / (400 * g)) * lam ^ 2 * (T : ℝ) + lam * a) := by
    rw [hspace, htime_eq]
    linarith
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ _ := hraw
    _ ≤ Real.exp (1 / 200 + (-(1 / (400 * g)) * lam ^ 2 * (T : ℝ) + lam * a)) :=
      Real.exp_le_exp.mpr harg
    _ = _ := Real.exp_add _ _



end EinsteinFull.Regeneration
