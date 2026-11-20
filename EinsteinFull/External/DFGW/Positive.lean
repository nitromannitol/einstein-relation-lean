import EinsteinFull.External.DFGW.OperatorSemigroup

/-! # Positivity of stationary correlations

A reversible continuous-time transition operator is the square of a self-adjoint operator.
Its quadratic form, and hence each diagonal velocity correlation, is nonnegative.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- A reversible transition operator has a nonnegative quadratic form. -/
theorem inner_transitionOperator_nonneg (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (t : ℝ≥0) (f : Lp ℝ 2 μ) : 0 ≤ inner ℝ f (transitionOperator hP t f) := by
  have ht : t / 2 + t / 2 = t := add_halves t
  have hfact : transitionOperator hP t =
      (transitionOperator hP (t / 2)).comp (transitionOperator hP (t / 2)) := by
    calc
      transitionOperator hP t = transitionOperator hP (t / 2 + t / 2) := by rw [ht]
      _ = _ := transitionOperator_add hP (t / 2) (t / 2)
  have heq : inner ℝ f (transitionOperator hP t f) =
      inner ℝ (transitionOperator hP (t / 2) f) (transitionOperator hP (t / 2) f) := by
    rw [hfact]
    exact (inner_transitionOperator hP (t / 2) f (transitionOperator hP (t / 2) f)).symm
  rw [heq]
  exact real_inner_self_nonneg

/-- The two-time autocorrelation of an `L²` observable is nonnegative. -/
theorem integral_mul_kernel_nonneg (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (t : ℝ≥0) (f : Lp ℝ 2 μ) :
    0 ≤ ∫ x, f x * ∫ y, f y ∂T t x ∂μ := by
  have h := inner_transitionOperator_nonneg hP t f
  rw [L2.inner_def] at h
  have he : (∫ x, inner ℝ (f x) (transitionOperator hP t f x) ∂μ) =
      ∫ x, f x * ∫ y, f y ∂T t x ∂μ := by
    apply integral_congr_ae
    filter_upwards [transitionOperator_ae_eq hP t f] with x hx
    simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial, hx, mul_comm]
  rw [he] at h
  exact h

end EinsteinFull.External.DFGW
