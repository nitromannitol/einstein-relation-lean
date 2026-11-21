import EinsteinFull.External.DFGW.KernelSymmetry
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Correlations of continuous observables

Continuity of trajectories and dominated convergence give continuity at zero of the
correlations of bounded continuous state observables.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The correlation of bounded continuous observables is continuous at time zero. -/
theorem tendsto_correlation_zero (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (f g : S → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hfb : ∃ C, ∀ x, |f x| ≤ C) (hgb : ∃ C, ∀ x, |g x| ≤ C) :
    Tendsto (fun t : ℝ≥0 => ∫ x, (∫ y, f y ∂T t x) * g x ∂μ) (𝓝 0)
      (𝓝 (∫ x, f x * g x ∂μ)) := by
  let : IsProbabilityMeasure P := hP.probability
  obtain ⟨Cf, hCf⟩ := hfb
  obtain ⟨Cg, hCg⟩ := hgb
  let A : ℝ := |Cf| + 1
  let B : ℝ := |Cg| + 1
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hfA (x : S) : |f x| ≤ A := (hCf x).trans (by dsimp [A]; linarith [le_abs_self Cf])
  have hgB (x : S) : |g x| ≤ B := (hCg x).trans (by dsimp [B]; linarith [le_abs_self Cg])
  have hlim : Tendsto (fun t : ℝ≥0 => ∫ η : C(ℝ, S), f (η t) * g (η 0) ∂P) (𝓝 0)
      (𝓝 (∫ η : C(ℝ, S), f (η 0) * g (η 0) ∂P)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => A * B)
    · exact Eventually.of_forall fun t =>
        (((hf.measurable.comp (continuous_eval_const (t : ℝ)).measurable).mul
          (hg.measurable.comp (continuous_eval_const 0).measurable)).aestronglyMeasurable)
    · exact Eventually.of_forall fun t => ae_of_all P fun η => by
        simp only [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hfA (η t)) (hgB (η 0)) (abs_nonneg _) hA
    · exact integrable_const _
    · exact ae_of_all P fun η => by
        have h := (hf.comp η.continuous).tendsto (0 : ℝ)
        have ht := h.comp (NNReal.continuous_coe.tendsto 0)
        simpa only [NNReal.coe_zero, Function.comp_def] using ht.mul tendsto_const_nhds
  have hmap := integral_map (μ := P) (continuous_eval_const (0 : ℝ)).measurable.aemeasurable
    (f := fun x => f x * g x) (by rw [hP.marginal]; exact (hf.measurable.mul hg.measurable).aestronglyMeasurable)
  rw [hP.marginal] at hmap
  rw [hmap]
  refine hlim.congr' ?_
  exact Eventually.of_forall fun t =>
    (integral_kernel_mul_eq_correlation hP f g hf.measurable hg.measurable
      ⟨Cf, hCf⟩ ⟨Cg, hCg⟩ t).symm

end EinsteinFull.External.DFGW
