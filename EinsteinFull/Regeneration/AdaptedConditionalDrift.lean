import EinsteinFull.Regeneration.AdaptedBoundedDriftTail

/-!
# Concentration from conditional drift

A bounded adapted sequence with positive conditional drift has an exponentially
small lower tail.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal ENNReal ProbabilityTheory

namespace EinsteinFull.Regeneration

/-- A bounded adapted sequence with positive conditional drift has an exponential
lower tail. -/
theorem adapted_walk_lower_tail_of_conditional_drift {Ω : Type*}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (X : ℕ → Ω → ℝ)
    (hX : StronglyAdapted ℱ X)
    (hbound : ∀ j, ∀ᵐ ω ∂μ, X j ω ∈ Set.Icc (-1 : ℝ) 1)
    (hmean0 : (1 / 5 : ℝ) ≤ ∫ ω, X 0 ω ∂μ)
    (hdrift : ∀ j, ∀ᵐ ω ∂μ, (1 / 5 : ℝ) ≤ μ[X (j + 1) | ℱ j] ω)
    (n : ℕ) (a : ℝ) :
    μ.real {ω | ∑ j ∈ range n, X j ω ≤ a} ≤ Real.exp (a / 20 - (n : ℝ) / 200) := by
  let M : ℕ → Ω → ℝ
    | 0 => fun _ => ∫ ω, X 0 ω ∂μ
    | j + 1 => μ[X (j + 1) | ℱ j]
  have hXm (j : ℕ) : Measurable (X j) := ((hX j).mono (ℱ.le j)).measurable
  have hXi (j : ℕ) : Integrable (X j) μ :=
    Integrable.of_mem_Icc (-1) 1 (hXm j).aemeasurable (hbound j)
  have hM : StronglyAdapted ℱ M := by
    intro j
    cases j with
    | zero => exact stronglyMeasurable_const
    | succ j => exact stronglyMeasurable_condExp.mono (ℱ.mono (Nat.le_succ j))
  have hadapt : StronglyAdapted ℱ (fun j ω => M j ω - X j ω) := hM.sub hX
  have hY (j : ℕ) : Measurable (fun ω => M j ω - X j ω) :=
    ((hadapt j).mono (ℱ.le j)).measurable
  have hM0lo : (-1 : ℝ) ≤ ∫ ω, X 0 ω ∂μ := by
    simpa using integral_mono_ae (integrable_const (-1 : ℝ)) (hXi 0)
      ((hbound 0).mono fun ω h => h.1)
  have hM0hi : (∫ ω, X 0 ω ∂μ) ≤ (1 : ℝ) := by
    simpa using integral_mono_ae (hXi 0) (integrable_const (1 : ℝ))
      ((hbound 0).mono fun ω h => h.2)
  have hYbound (j : ℕ) : ∀ᵐ ω ∂μ, M j ω - X j ω ∈ Set.Icc (-2 : ℝ) 2 := by
    cases j with
    | zero =>
      filter_upwards [hbound 0] with ω h
      change (∫ ω, X 0 ω ∂μ) - X 0 ω ∈ Set.Icc (-2 : ℝ) 2
      exact ⟨by linarith [h.2], by linarith [h.1]⟩
    | succ j =>
      exact (bounded_conditional_centering μ (ℱ j) (ℱ.le j) (X (j + 1))
        (hXm (j + 1)) (hbound (j + 1))).2.1
  have hYmean0 : (∫ ω, (M 0 ω - X 0 ω) ∂μ) = 0 := by
    change (∫ ω, ((∫ ω, X 0 ω ∂μ) - X 0 ω) ∂μ) = 0
    rw [integral_sub (integrable_const _) (hXi 0)]
    simp
  have hYmean (j : ℕ) : μ[fun ω => M (j + 1) ω - X (j + 1) ω | ℱ j] =ᵐ[μ] (fun _ => 0) :=
    (bounded_conditional_centering μ (ℱ j) (ℱ.le j) (X (j + 1))
      (hXm (j + 1)) (hbound (j + 1))).2.2
  have hMdrift (j : ℕ) : ∀ᵐ ω ∂μ, (1 / 5 : ℝ) ≤ M j ω := by
    cases j with
    | zero => exact Filter.Eventually.of_forall (fun _ => hmean0)
    | succ j => exact hdrift j
  exact adapted_walk_lower_tail_of_bounded_fluctuations μ ℱ X M hadapt hY hYbound
    hYmean0 hYmean hMdrift n a

end EinsteinFull.Regeneration
