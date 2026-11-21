import EinsteinFull.External.DFGW.OpenCorrelation
import EinsteinFull.External.DFGW.StrongContinuity

/-! # Strong continuity for open-set indicators

Open-set autocorrelation continuity implies strong `L²` continuity for the corresponding
indicator vector.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The orbit of the indicator of an open set is strongly continuous at zero. -/
theorem tendsto_transitionOperator_open_indicator (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    {A : Set S} (hA : IsOpen A) (hμA : μ A ≠ ∞) :
    Tendsto (fun t : ℝ≥0 => transitionOperator hP t
      (indicatorConstLp 2 hA.measurableSet hμA (1 : ℝ))) (𝓝 0)
      (𝓝 (indicatorConstLp 2 hA.measurableSet hμA (1 : ℝ))) := by
  let : IsProbabilityMeasure μ := hP.invariant_probability
  let f : Lp ℝ 2 μ := indicatorConstLp 2 hA.measurableSet hμA (1 : ℝ)
  let u : S → ℝ := A.indicator (fun _ => (1 : ℝ))
  have hfu : f =ᵐ[μ] u := indicatorConstLp_coeFn
  have hc (t : ℝ≥0) : inner ℝ f (transitionOperator hP t f) =
      ∫ x, (∫ y, u y ∂T t x) * u x ∂μ := by
    have hkernel := MarkovProcess.kernelIntegral_congr_ae
      (le_of_eq (kernel_comp_eq hP t)) hfu
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hfu, transitionOperator_ae_eq hP t f, hkernel] with x hx ht hk
    change inner ℝ (f x) ((transitionOperator hP t f) x) = _
    rw [ht]
    change inner ℝ (f x) (MarkovProcess.kernelIntegral (T t) f x) = _
    rw [hx, hk]
    simp only [MarkovProcess.kernelIntegral, RCLike.inner_apply, starRingEnd_apply,
      star_trivial]
  have hnorm : ‖f‖ ^ 2 = ∫ x, u x ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hfu] with x hx
    rw [hx]
    simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial, pow_two]
  have hlim := tendsto_open_indicator_correlation_zero hP hA
  change Tendsto (fun t : ℝ≥0 => ∫ x, (∫ y, u y ∂T t x) * u x ∂μ) (𝓝 0)
    (𝓝 (∫ x, u x ^ 2 ∂μ)) at hlim
  rw [← hnorm] at hlim
  apply tendsto_transitionOperator_of_correlation hP f
  refine hlim.congr' ?_
  exact Eventually.of_forall fun t => (hc t).symm

end EinsteinFull.External.DFGW
