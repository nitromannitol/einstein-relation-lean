import EinsteinFull.External.DFGW.KernelSymmetry
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Correlations of open-set indicators

For a continuous trajectory, a state initially in an open set remains in that set for a
short time. The corresponding stationary correlation is continuous at zero.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The autocorrelation of an open-set indicator converges to its initial second moment. -/
theorem tendsto_open_indicator_correlation_zero (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    {A : Set S} (hA : IsOpen A) :
    Tendsto (fun t : ℝ≥0 => ∫ x, (∫ y, A.indicator (fun _ => (1 : ℝ)) y ∂T t x) *
      A.indicator (fun _ => (1 : ℝ)) x ∂μ) (𝓝 0)
      (𝓝 (∫ x, A.indicator (fun _ => (1 : ℝ)) x ^ 2 ∂μ)) := by
  let : IsProbabilityMeasure P := hP.probability
  let f : S → ℝ := A.indicator (fun _ => (1 : ℝ))
  have hf : Measurable f := measurable_const.indicator hA.measurableSet
  have hfb : ∃ C, ∀ x, |f x| ≤ C := ⟨1, fun x => by
    dsimp only [f]
    by_cases hx : x ∈ A <;> simp [hx]⟩
  have hlim : Tendsto (fun t : ℝ≥0 => ∫ η : C(ℝ, S), f (η t) * f (η 0) ∂P) (𝓝 0)
      (𝓝 (∫ η : C(ℝ, S), f (η 0) ^ 2 ∂P)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => 1)
    · exact Eventually.of_forall fun t =>
        (((hf.comp (continuous_eval_const (t : ℝ)).measurable).mul
          (hf.comp (continuous_eval_const 0).measurable)).aestronglyMeasurable)
    · refine Eventually.of_forall fun t => ae_of_all P fun η => ?_
      dsimp only [f]
      by_cases ha : η 0 ∈ A <;> by_cases hb : η t ∈ A <;> simp [ha, hb]
    · exact integrable_const _
    · refine ae_of_all P fun η => ?_
      by_cases hη : η 0 ∈ A
      · have ht : Tendsto (fun t : ℝ≥0 => η t) (𝓝 0) (𝓝 (η 0)) := by
          simpa only [NNReal.coe_zero, Function.comp_def] using
            (η.continuous.tendsto (0 : ℝ)).comp (NNReal.continuous_coe.tendsto 0)
        have he : ∀ᶠ t : ℝ≥0 in 𝓝 0, η t ∈ A := ht (hA.mem_nhds hη)
        have heq : (fun t : ℝ≥0 => f (η t) * f (η 0)) =ᶠ[𝓝 0] fun _ => (1 : ℝ) := by
          filter_upwards [he] with t ht'
          simp [f, hη, ht']
        have hgoal : f (η 0) ^ 2 = 1 := by simp [f, hη]
        rw [hgoal]
        exact tendsto_const_nhds.congr' heq.symm
      · have hzero : f (η 0) = 0 := by simp [f, hη]
        simp [hzero]
  have hmap := integral_map (μ := P) (continuous_eval_const (0 : ℝ)).measurable.aemeasurable
    (f := fun x => f x ^ 2) (by rw [hP.marginal]; exact (hf.pow_const 2).aestronglyMeasurable)
  rw [hP.marginal] at hmap
  change Tendsto (fun t : ℝ≥0 => ∫ x, (∫ y, f y ∂T t x) * f x ∂μ) (𝓝 0)
    (𝓝 (∫ x, f x ^ 2 ∂μ))
  rw [hmap]
  refine hlim.congr' ?_
  exact Eventually.of_forall fun t => (integral_kernel_mul_eq_correlation hP f f hf hf hfb hfb t).symm

end EinsteinFull.External.DFGW
