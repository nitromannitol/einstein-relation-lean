import Mathlib.Probability.Moments.SubGaussian

/-!
# A lower-tail estimate for a biased walk

The comparison walk in Gantert–Mathieu–Piatnitski, proof of Lemma 4.2, has independent
increments in `[-1,1]` with mean `1/5`. Its lower tail decays exponentially with the number
of steps. The estimate also applies to any independent increments with those bounds and means.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ProbabilityTheory NNReal

namespace EinsteinFull.Regeneration

/-- Independent increments bounded by one and of mean `1/5` satisfy the exponential
lower-tail bound used for the biased comparison walk in GMP, Lemma 4.2. -/
theorem biased_walk_lower_tail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (-1 : ℝ) 1)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) = (1 / 5 : ℝ)) (n : ℕ) (a : ℝ) :
    μ.real {ω | ∑ i ∈ range n, X i ω ≤ a} ≤ Real.exp (a / 5 - (n : ℝ) / 50) := by
  let Y : ℕ → Ω → ℝ := fun i ω => (1 / 5 : ℝ) - X i ω
  have hY : iIndepFun Y μ := by
    simpa only [Y, Function.comp_def] using
      hind.comp (fun (_ : ℕ) (x : ℝ) => (1 / 5 : ℝ) - x) (fun _ => by fun_prop)
  have hsub (i : ℕ) : HasSubgaussianMGF (Y i) 1 μ := by
    have h := hasSubgaussianMGF_of_mem_Icc (hX i).aemeasurable (hbound i)
    rw [hmean i] at h
    have h' := h.neg
    convert h' using 1 <;> norm_num [Y, Pi.neg_apply]
    funext ω
    simp only [Pi.neg_apply]
    ring
  have hsum : HasSubgaussianMGF (fun ω => ∑ i ∈ range n, Y i ω) (n : ℝ≥0) μ := by
    convert HasSubgaussianMGF.sum_of_iIndepFun hY (s := range n) (c := fun _ => 1)
      (fun i _ => hsub i) using 1; simp
  have hchernoff := measure_ge_le_exp_mul_mgf (X := fun ω => ∑ i ∈ range n, Y i ω)
    (μ := μ) ((n : ℝ) / 5 - a) (t := (1 / 5 : ℝ)) (by norm_num)
    (hsum.integrable_exp_mul _)
  have hevents : {ω | ∑ i ∈ range n, X i ω ≤ a} =
      {ω | (n : ℝ) / 5 - a ≤ ∑ i ∈ range n, Y i ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Y, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
    constructor <;> intro h <;> linarith
  rw [hevents]
  calc
    _ ≤ Real.exp (-(1 / 5 : ℝ) * ((n : ℝ) / 5 - a)) *
        mgf (fun ω => ∑ i ∈ range n, Y i ω) μ (1 / 5) := hchernoff
    _ ≤ Real.exp (-(1 / 5 : ℝ) * ((n : ℝ) / 5 - a)) *
        Real.exp ((n : ℝ) * (1 / 5 : ℝ) ^ 2 / 2) := by
      gcongr
      exact hsum.mgf_le _
    _ = Real.exp (a / 5 - (n : ℝ) / 50) := by
      rw [← Real.exp_add]
      congr 1
      ring

end EinsteinFull.Regeneration
