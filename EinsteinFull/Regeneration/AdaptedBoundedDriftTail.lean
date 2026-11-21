import EinsteinFull.Regeneration.AdaptedSlabWalkTail
import EinsteinFull.Regeneration.ConditionalBoundedSubgaussian

/-!
# Lower tails from bounded adapted increments

Conditional centering and boundedness give the concentration estimate for
adapted increments with a positive predictable drift.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ProbabilityTheory NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- A predictable drift lower bound and conditionally sub-Gaussian fluctuations
imply the exponential lower-tail estimate used in the slab comparison. -/
theorem adapted_walk_lower_tail_of_four_subgaussian {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)
    (X M : ℕ → Ω → ℝ)
    (hadapt : StronglyAdapted ℱ (fun j ω => M j ω - X j ω))
    (h0 : HasSubgaussianMGF (fun ω => M 0 ω - X 0 ω) 4 μ)
    (hcond : ∀ j, HasCondSubgaussianMGF (ℱ j) (ℱ.le j)
      (fun ω => M (j + 1) ω - X (j + 1) ω) 4 μ)
    (hdrift : ∀ j, ∀ᵐ ω ∂μ, (1 / 5 : ℝ) ≤ M j ω)
    (n : ℕ) (a : ℝ) :
    μ.real {ω | ∑ j ∈ range n, X j ω ≤ a} ≤ Real.exp (a / 20 - (n : ℝ) / 200) := by
  let Y : ℕ → Ω → ℝ := fun j ω => M j ω - X j ω
  have hsum : HasSubgaussianMGF (fun ω => ∑ j ∈ range n, Y j ω) (4 * n : ℝ≥0) μ := by
    convert HasSubgaussianMGF.sum_of_hasCondSubgaussianMGF (μ := μ) (cY := fun _ => 4) hadapt h0 n
      (fun j _ => hcond j) using 1
    simp [mul_comm]
  have hchernoff := measure_ge_le_exp_mul_mgf (X := fun ω => ∑ j ∈ range n, Y j ω)
    (μ := μ) ((n : ℝ) / 5 - a) (t := (1 / 20 : ℝ)) (by norm_num)
    (hsum.integrable_exp_mul _)
  have hdrift' : ∀ᵐ ω ∂μ, ∀ j, (1 / 5 : ℝ) ≤ M j ω := ae_all_iff.mpr hdrift
  have hsub : ∀ᵐ ω ∂μ, ω ∈ {ω | ∑ j ∈ range n, X j ω ≤ a} →
      ω ∈ {ω | (n : ℝ) / 5 - a ≤ ∑ j ∈ range n, Y j ω} := by
    filter_upwards [hdrift'] with ω hω hx
    have hM : (n : ℝ) / 5 ≤ ∑ j ∈ range n, M j ω := by
      calc
        _ = ∑ _j ∈ range n, (1 / 5 : ℝ) := by simp; ring
        _ ≤ _ := sum_le_sum (fun j _ => hω j)
    simp only [Y, sum_sub_distrib] at hx ⊢
    linarith
  have hmeasure : μ.real {ω | ∑ j ∈ range n, X j ω ≤ a} ≤
      μ.real {ω | (n : ℝ) / 5 - a ≤ ∑ j ∈ range n, Y j ω} :=
    ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hsub)
  calc
    _ ≤ _ := hmeasure
    _ ≤ Real.exp (-(1 / 20 : ℝ) * ((n : ℝ) / 5 - a)) *
        mgf (fun ω => ∑ j ∈ range n, Y j ω) μ (1 / 20) := hchernoff
    _ ≤ Real.exp (-(1 / 20 : ℝ) * ((n : ℝ) / 5 - a)) *
        Real.exp (4 * (n : ℝ) * (1 / 20 : ℝ) ^ 2 / 2) := by
      gcongr
      exact hsum.mgf_le _
    _ = Real.exp (a / 20 - (n : ℝ) / 200) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- Bounded centered fluctuations and a drift of at least one fifth imply an
exponential lower tail without an independent comparison sequence. -/
theorem adapted_walk_lower_tail_of_bounded_fluctuations {Ω : Type*}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (X M : ℕ → Ω → ℝ)
    (hadapt : StronglyAdapted ℱ (fun j ω => M j ω - X j ω))
    (hY : ∀ j, Measurable (fun ω => M j ω - X j ω))
    (hbound : ∀ j, ∀ᵐ ω ∂μ, M j ω - X j ω ∈ Set.Icc (-2 : ℝ) 2)
    (hmean0 : (∫ ω, (M 0 ω - X 0 ω) ∂μ) = 0)
    (hmean : ∀ j, μ[fun ω => M (j + 1) ω - X (j + 1) ω | ℱ j] =ᵐ[μ] (fun _ => 0))
    (hdrift : ∀ j, ∀ᵐ ω ∂μ, (1 / 5 : ℝ) ≤ M j ω) (n : ℕ) (a : ℝ) :
    μ.real {ω | ∑ j ∈ range n, X j ω ≤ a} ≤ Real.exp (a / 20 - (n : ℝ) / 200) := by
  have h0 : HasSubgaussianMGF (fun ω => M 0 ω - X 0 ω) 4 μ := by
    have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      (hY 0).aemeasurable (hbound 0) hmean0
    convert h using 1
    norm_num
  have hc (j : ℕ) : HasCondSubgaussianMGF (ℱ j) (ℱ.le j)
      (fun ω => M (j + 1) ω - X (j + 1) ω) 4 μ :=
    bounded_conditional_centered_subgaussian μ (ℱ j) (ℱ.le j)
      (fun ω => M (j + 1) ω - X (j + 1) ω) (hY (j + 1)) (hbound (j + 1)) (hmean j)
  exact adapted_walk_lower_tail_of_four_subgaussian μ ℱ X M hadapt h0 hc hdrift n a

end EinsteinFull.Regeneration
