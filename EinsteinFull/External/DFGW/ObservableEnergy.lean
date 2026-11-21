import EinsteinFull.External.DFGW.CorrelationRepresentation
import EinsteinFull.External.DFGW.KernelSymmetry

/-! # Energy of state-observable increments

The mean square increment of a stationary state observable is twice its finite-time semigroup
energy. This identity connects the reflection pairing with the energy of the Markov process.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The mean square increment of a bounded observable equals twice its semigroup energy. -/
theorem integral_observable_increment_sq (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (f : S → ℝ) (hf : Measurable f) (hfb : ∃ C, ∀ x, |f x| ≤ C)
    (hfL2 : MemLp f 2 μ) (t : ℝ≥0) :
    (∫ η : C(ℝ, S), (f (η t) - f (η 0)) ^ 2 ∂P) =
      2 * (‖hfL2.toLp f‖ ^ 2 - inner ℝ (hfL2.toLp f)
        (transitionOperator hP t (hfL2.toLp f))) := by
  let : IsProbabilityMeasure P := hP.probability
  have heval (r : ℝ) : MeasurePreserving (fun η : C(ℝ, S) => η r) P μ :=
    ⟨(continuous_eval_const r).measurable, hP.marginal r⟩
  have hF (r : ℝ) : MemLp (fun η : C(ℝ, S) => f (η r)) 2 P :=
    hfL2.comp_measurePreserving (heval r)
  have hsq (r : ℝ) : (∫ η : C(ℝ, S), f (η r) ^ 2 ∂P) = ∫ x, f x ^ 2 ∂μ := by
    have hmap := integral_map (μ := P) (continuous_eval_const r).measurable.aemeasurable
      (f := fun x => f x ^ 2) (by rw [hP.marginal]; exact hfL2.integrable_sq.aestronglyMeasurable)
    rw [hP.marginal] at hmap
    exact hmap.symm
  have hnorm : ‖hfL2.toLp f‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp hfL2] with x hx
    rw [hx]
    simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial, pow_two]
  have hcross : (∫ η : C(ℝ, S), f (η t) * f (η 0) ∂P) =
      inner ℝ (hfL2.toLp f) (transitionOperator hP t (hfL2.toLp f)) := by
    calc
      (∫ η : C(ℝ, S), f (η t) * f (η 0) ∂P) =
          ∫ x, (∫ y, f y ∂T t x) * f x ∂μ :=
        (integral_kernel_mul_eq_correlation hP f f hf hf hfb hfb t).symm
      _ = inner ℝ (hfL2.toLp f) (transitionOperator hP t (hfL2.toLp f)) := by
        simpa only [mul_comm] using integral_mul_kernel_eq_inner hP t f f hfL2 hfL2
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
