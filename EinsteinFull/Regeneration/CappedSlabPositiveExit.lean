import EinsteinFull.Regeneration.CappedSlabRestart

/-!
# Forward hitting from a positive capped exit

A bounded increment with sufficiently high probability of its maximal value
has positive mean. Combined with the stopped restart law, this gives the
forward-hitting estimate from the capped-exit probability.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- A bounded variable is bounded below by twice its maximal-value indicator minus one. -/
theorem integral_lower_of_maximum_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X)
    (hbound : ∀ ω, X ω ∈ Set.Icc (-1 : ℝ) 1) :
    2 * μ.real {ω | X ω = 1} - 1 ≤ ∫ ω, X ω ∂μ := by
  let A : Set Ω := {ω | X ω = 1}
  have hA : MeasurableSet A := measurableSet_eq_fun hX measurable_const
  have hXi : Integrable X μ := Integrable.of_bound hX.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_le]
      exact hbound ω)
  have hIi : Integrable (A.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hA
  have hle : ∀ ω, 2 * A.indicator (fun _ => (1 : ℝ)) ω - 1 ≤ X ω := by
    intro ω
    by_cases hω : ω ∈ A
    · have hx : X ω = 1 := hω
      simp [hω, hx]
      norm_num
    · simp only [Set.indicator_of_notMem hω, mul_zero, zero_sub]
      exact (hbound ω).1
  have h := integral_mono_ae ((hIi.const_mul 2).sub (integrable_const 1)) hXi
    (Filter.Eventually.of_forall hle)
  change (∫ ω, 2 * A.indicator (fun _ => (1 : ℝ)) ω - 1 ∂μ) ≤ ∫ ω, X ω ∂μ at h
  rw [integral_sub (hIi.const_mul 2) (integrable_const 1), integral_const_mul] at h
  change 2 * (∫ ω, A.indicator (1 : Ω → ℝ) ω ∂μ) - (∫ _ : Ω, (1 : ℝ) ∂μ) ≤ _ at h
  rw [integral_indicator_one hA] at h
  simpa only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul, A] using h

/-- A positive capped-exit probability gives a positive mean for the initial slab step. -/
theorem initial_slab_mean_of_positive_exit {d : ℕ} (μ : Measure (Path d))
    [IsProbabilityMeasure μ] (i : Fin d) (r : ℝ) (hr : 0 < r) (g : ℝ≥0)
    (hpositive : (3 / 5 : ℝ) ≤ μ.real {γ | cappedSlabIncrement γ i r g 0 = 1}) :
    (1 / 5 : ℝ) ≤ ∫ γ, cappedSlabIncrement γ i r g 0 ∂μ := by
  have h := integral_lower_of_maximum_probability μ
    (fun γ => cappedSlabIncrement γ i r g 0) (measurable_cappedSlabIncrement i r g 0)
    (fun γ => cappedSlabIncrement_mem_Icc γ i r hr g 0)
  linarith

/-- The positive-exit estimate in the proof of GMP Lemma 4.2 yields forward hitting. -/
theorem forward_hitting_le_of_regular_positive_exit {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I)
    (x : Vec d) (i : Fin d) (L g : ℝ) (hlam : 0 < lam)
    (hL : (1 / 20 : ℝ) ≤ L) (hg : 0 < g)
    (hpositive : ∀ y : Vec d, (3 / 5 : ℝ) ≤ (K y).real
      {γ | cappedSlabIncrement γ i (L / lam) (Real.toNNReal (g / lam ^ 2)) 0 = 1})
    (T : ℝ≥0) (a : ℝ) (ha : 0 ≤ a) :
    K x {γ | (T : ℝ≥0∞) ≤ firstHittingAbove γ i a} ≤
      ENNReal.ofReal (Real.exp (1 / 200) *
        Real.exp (-(1 / (400 * g)) * lam ^ 2 * (T : ℝ) + lam * a)) := by
  apply forward_hitting_le_of_regular_initial_slab_mean hd ω lam Λ hΛ hω K hfdd
    x i L g hlam hL hg
  · intro y
    exact initial_slab_mean_of_positive_exit (K y) i (L / lam)
      (div_pos (by linarith) hlam) (Real.toNNReal (g / lam ^ 2)) (hpositive y)
  · exact ha

end EinsteinFull.Regeneration
