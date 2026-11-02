import Mathlib.MeasureTheory.Function.L2Space

/-!
# Literal representative errors detect spatial L² convergence

Source: `paper/main.tex:693-698,727-729`. The squared Euclidean L² norm
is exactly the integral of the squared pointwise norm, independently of
chosen representatives.
-/

open MeasureTheory Filter Topology
noncomputable section
namespace EinsteinRelation.Correctors

/-- The norm of the actual L² class is the unnormalized spatial square norm. -/
theorem norm_toLp_eq_sqrt_integral_norm_sq
    {A E : Type*} [MeasurableSpace A] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (μ : Measure A) (f : A → E) (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ = Real.sqrt (∫ a, ‖f a‖ ^ 2 ∂μ) := by
  have hsq : ‖hf.toLp f‖ ^ 2 = ∫ a, ‖f a‖ ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with a ha
    rw [ha, real_inner_self_eq_norm_sq]
  rw [← hsq, Real.sqrt_sq (norm_nonneg _)]

/-- Convergence of literal representative errors implies convergence of
spatial L² classes. -/
theorem tendsto_toLp_of_integral_sq_norm_sub_tendsto_zero
    {A E : Type*} [MeasurableSpace A] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (μ : Measure A) (f : ℕ → A → E) (g : A → E)
    (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ)
    (hlim : Tendsto (fun n => ∫ a, ‖f n a - g a‖ ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have h0 := (Real.continuous_sqrt.tendsto 0).comp hlim
  rw [Real.sqrt_zero] at h0
  have h : Tendsto (fun n => Real.sqrt (∫ a, ‖f n a - g a‖ ^ 2 ∂μ)) atTop (𝓝 0) := h0
  refine Tendsto.congr (fun n => ?_) h
  rw [← MemLp.toLp_sub (hf n) hg, norm_toLp_eq_sqrt_integral_norm_sq]
  rfl

end EinsteinRelation.Correctors
