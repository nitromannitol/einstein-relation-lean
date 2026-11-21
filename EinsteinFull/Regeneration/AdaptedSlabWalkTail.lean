import Mathlib.Probability.Moments.SubGaussian

/-!
# Lower tails for adapted comparison increments

Conditional sub-Gaussian centered increments with positive predictable drift
obey the same exponential lower-tail estimate as the biased comparison walk.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ProbabilityTheory NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- A predictable drift lower bound and conditionally sub-Gaussian fluctuations
imply the exponential lower-tail estimate used in the slab comparison. -/
theorem adapted_walk_lower_tail {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)
    (X M : ℕ → Ω → ℝ)
    (hadapt : StronglyAdapted ℱ (fun j ω => M j ω - X j ω))
    (h0 : HasSubgaussianMGF (fun ω => M 0 ω - X 0 ω) 1 μ)
    (hcond : ∀ j, HasCondSubgaussianMGF (ℱ j) (ℱ.le j)
      (fun ω => M (j + 1) ω - X (j + 1) ω) 1 μ)
    (hdrift : ∀ j, ∀ᵐ ω ∂μ, (1 / 5 : ℝ) ≤ M j ω)
    (n : ℕ) (a : ℝ) :
    μ.real {ω | ∑ j ∈ range n, X j ω ≤ a} ≤ Real.exp (a / 5 - (n : ℝ) / 50) := by
  let Y : ℕ → Ω → ℝ := fun j ω => M j ω - X j ω
  have hsum : HasSubgaussianMGF (fun ω => ∑ j ∈ range n, Y j ω) (n : ℝ≥0) μ := by
    convert HasSubgaussianMGF.sum_of_hasCondSubgaussianMGF (μ := μ) (cY := fun _ => 1) hadapt h0 n
      (fun j _ => hcond j) using 1
    simp
  have hchernoff := measure_ge_le_exp_mul_mgf (X := fun ω => ∑ j ∈ range n, Y j ω)
    (μ := μ) ((n : ℝ) / 5 - a) (t := (1 / 5 : ℝ)) (by norm_num)
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
    _ ≤ Real.exp (-(1 / 5 : ℝ) * ((n : ℝ) / 5 - a)) *
        mgf (fun ω => ∑ j ∈ range n, Y j ω) μ (1 / 5) := hchernoff
    _ ≤ Real.exp (-(1 / 5 : ℝ) * ((n : ℝ) / 5 - a)) *
        Real.exp ((n : ℝ) * (1 / 5 : ℝ) ^ 2 / 2) := by
      gcongr
      exact hsum.mgf_le _
    _ = Real.exp (a / 5 - (n : ℝ) / 50) := by
      rw [← Real.exp_add]
      congr 1
      ring

end EinsteinFull.Regeneration
