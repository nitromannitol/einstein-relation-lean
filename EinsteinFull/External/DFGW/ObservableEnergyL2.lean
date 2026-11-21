import EinsteinFull.External.DFGW.TwoTimeCorrelation
import EinsteinFull.External.DFGW.ObservableEnergy

/-! # Energy of square-integrable observable increments

The mean-square increment of any square-integrable stationary observable is twice its
finite-time semigroup energy.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The mean square of a stationary `L²` observable increment equals its semigroup energy. -/
theorem integral_L2_observable_increment_sq (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (f : Lp ℝ 2 μ) (t : ℝ≥0) :
    (∫ η : C(ℝ, S), (f (η t) - f (η 0)) ^ 2 ∂P) =
      2 * (‖f‖ ^ 2 - inner ℝ f (transitionOperator hP t f)) := by
  let : IsProbabilityMeasure P := hP.probability
  have heval (r : ℝ) : MeasurePreserving (fun η : C(ℝ, S) => η r) P μ :=
    ⟨(continuous_eval_const r).measurable, hP.marginal r⟩
  have hF (r : ℝ) : MemLp (fun η : C(ℝ, S) => f (η r)) 2 P :=
    (Lp.memLp f).comp_measurePreserving (heval r)
  have hsq (r : ℝ) : (∫ η : C(ℝ, S), f (η r) ^ 2 ∂P) = ∫ x, f x ^ 2 ∂μ := by
    have hmap := integral_map (μ := P) (continuous_eval_const r).measurable.aemeasurable
      (f := fun x => f x ^ 2) (by rw [hP.marginal]; exact (Lp.memLp f).integrable_sq.aestronglyMeasurable)
    rw [hP.marginal] at hmap
    exact hmap.symm
  have hnorm : ‖f‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards with x
    simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial, pow_two]
  have hcross : (∫ η : C(ℝ, S), f (η t) * f (η 0) ∂P) =
      inner ℝ f (transitionOperator hP t f) := by
    have h := integral_eval_zero_mul_eval hP f f (Lp.memLp f) (Lp.memLp f) t
    have hto : (Lp.memLp f).toLp f = f := by
      apply Lp.ext
      exact MemLp.coeFn_toLp (Lp.memLp f)
    rw [hto] at h
    simpa only [mul_comm] using h
  have heq : (fun η : C(ℝ, S) => (f (η t) - f (η 0)) ^ 2) =
      (fun η => f (η t) ^ 2) + (fun η => f (η 0) ^ 2) -
        (fun η => 2 * (f (η t) * f (η 0))) := by
    funext η
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have hcrossint : Integrable (fun η : C(ℝ, S) => 2 * (f (η t) * f (η 0))) P :=
    ((hF t).integrable_mul (hF 0)).const_mul 2
  have hsumint : Integrable (fun η : C(ℝ, S) => f (η t) ^ 2 + f (η 0) ^ 2) P :=
    ((hF t).integrable_sq.add (hF 0).integrable_sq)
  rw [heq]
  change (∫ η : C(ℝ, S), (f (η t) ^ 2 + f (η 0) ^ 2) -
    2 * (f (η t) * f (η 0)) ∂P) = _
  rw [integral_sub hsumint hcrossint,
    integral_add (hF t).integrable_sq (hF 0).integrable_sq, integral_const_mul,
    hsq, hsq, ← hnorm, hcross]
  ring

end EinsteinFull.External.DFGW
