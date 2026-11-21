import EinsteinFull.Regeneration.ForwardHittingFromAdaptedSlabs
import EinsteinFull.Regeneration.AdaptedBoundedDriftTail

/-!
# Forward hitting from bounded adapted slab increments

Bounded centered fluctuations and positive conditional drift yield the source
scaled forward-hitting estimate along the actual capped slab clock.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration Finset
open scoped NNReal ENNReal ProbabilityTheory

namespace EinsteinFull.Regeneration

/-- A lower-tail estimate for a comparison walk gives a forward-hitting tail.
The path and comparison walk live on the same probability space. -/
theorem forward_hitting_le_of_weaker_lower_tails {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ} (γ : Ω → Path d) (i : Fin d)
    (X : ℕ → Ω → ℝ)
    (htail : ∀ n a, μ.real {ω | ∑ j ∈ range n, X j ω ≤ a} ≤
      Real.exp (a / 20 - (n : ℝ) / 200))
    (τ : ℕ → Ω → ℝ≥0) (L g : ℝ) (hL : 0 < L) (hg : 0 < g)
    (htime : ∀ n, ∀ᵐ ω ∂μ, (τ n ω : ℝ) ≤ n * g)
    (hcompare : ∀ n, ∀ᵐ ω ∂μ,
      L * (∑ j ∈ range n, X j ω) ≤ γ ω (τ n ω) i - γ ω 0 i)
    (T : ℝ≥0) (a : ℝ) (ha : 0 ≤ a) :
    μ.real {ω | (T : ℝ≥0∞) ≤ firstHittingAbove (γ ω) i a} ≤
      Real.exp ((a / L) / 20 + 1 / 200 - (T : ℝ) / (400 * g)) := by
  by_cases hT : T = 0
  · subst T
    have he : 0 ≤ (a / L) / 20 + 1 / 200 := by positivity
    have h := (measureReal_le_one : μ.real {ω | ((0 : ℝ≥0) : ℝ≥0∞) ≤
      firstHittingAbove (γ ω) i a} ≤ 1).trans (Real.one_le_exp he)
    simpa only [NNReal.coe_zero, zero_div, sub_zero] using h
  · have hTpos : 0 < (T : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hT)
    let n : ℕ := ⌊(T : ℝ) / (2 * g)⌋₊
    have hdiv : 0 ≤ (T : ℝ) / (2 * g) := by positivity
    have hfloor : (n : ℝ) ≤ (T : ℝ) / (2 * g) := Nat.floor_le hdiv
    have hstep : (n : ℝ) * g < (T : ℝ) := by
      have h := (le_div_iff₀ (by positivity : 0 < 2 * g)).mp hfloor
      nlinarith
    have hsub : ∀ᵐ ω ∂μ, ω ∈ {ω | (T : ℝ≥0∞) ≤ firstHittingAbove (γ ω) i a} →
        ω ∈ {ω | ∑ j ∈ range n, X j ω ≤ a / L} := by
      filter_upwards [htime n, hcompare n] with ω ht hc hh
      have hτ : τ n ω < T := by
        apply NNReal.coe_lt_coe.mp
        exact lt_of_le_of_lt ht hstep
      have hcross : γ ω (τ n ω) i - γ ω 0 i < a := by
        by_contra hnot
        have hhit := firstHittingAbove_le_of_crossing (γ ω) i a (τ n ω) (le_of_not_gt hnot)
        have hlt : ((τ n ω : ℝ≥0) : ℝ≥0∞) < (T : ℝ≥0∞) := ENNReal.coe_lt_coe.mpr hτ
        exact (not_lt_of_ge (hh.trans hhit)) hlt
      apply (le_div_iff₀ hL).2
      nlinarith
    have hmeasure : μ.real {ω | (T : ℝ≥0∞) ≤ firstHittingAbove (γ ω) i a} ≤
        μ.real {ω | ∑ j ∈ range n, X j ω ≤ a / L} := by
      exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hsub)
    have hn : (T : ℝ) / (2 * g) < (n : ℝ) + 1 := Nat.lt_floor_add_one _
    have hexp : (a / L) / 20 - (n : ℝ) / 200 ≤
        (a / L) / 20 + 1 / 200 - (T : ℝ) / (400 * g) := by
      have he : (T : ℝ) / (2 * g) / 200 = (T : ℝ) / (400 * g) := by ring
      linarith
    exact hmeasure.trans ((htail n (a / L)).trans
      (Real.exp_le_exp.mpr hexp))

/-- Positive predictable drift and conditional sub-Gaussian fluctuations of the
actual capped increments imply the scaled forward-hitting estimate. -/
theorem forward_hitting_le_of_bounded_adapted_slabs {Ω : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d : ℕ} (γ : Ω → Path d) (i : Fin d) (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)
    (lam L g : ℝ) (hlam : 0 < lam) (hL : (1 / 20 : ℝ) ≤ L) (hg : 0 < g)
    (M : ℕ → Ω → ℝ)
    (hadapt : StronglyAdapted ℱ (fun j ω => M j ω -
      cappedSlabIncrement (γ ω) i (L / lam) (Real.toNNReal (g / lam ^ 2)) j))
    (hY : ∀ j, Measurable (fun ω => M j ω -
      cappedSlabIncrement (γ ω) i (L / lam) (Real.toNNReal (g / lam ^ 2)) j))
    (hbound : ∀ j, ∀ᵐ ω ∂μ, M j ω -
      cappedSlabIncrement (γ ω) i (L / lam) (Real.toNNReal (g / lam ^ 2)) j ∈
        Set.Icc (-2 : ℝ) 2)
    (hmean0 : (∫ ω, (M 0 ω - cappedSlabIncrement (γ ω) i (L / lam)
      (Real.toNNReal (g / lam ^ 2)) 0) ∂μ) = 0)
    (hmean : ∀ j, μ[fun ω => M (j + 1) ω - cappedSlabIncrement (γ ω) i (L / lam)
      (Real.toNNReal (g / lam ^ 2)) (j + 1) | ℱ j] =ᵐ[μ] (fun _ => 0))
    (hdrift : ∀ j, ∀ᵐ ω ∂μ, (1 / 5 : ℝ) ≤ M j ω)
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
  have htail := adapted_walk_lower_tail_of_bounded_fluctuations μ ℱ X M hadapt hY hbound hmean0 hmean hdrift
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
