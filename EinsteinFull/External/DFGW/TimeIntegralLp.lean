import EinsteinFull.External.DFGW.TimeIntegralBound

/-! # `L²` bounds for time-integrated observables

An integrated stationary observable is a trajectory `L²` vector, with norm bounded by elapsed
time times the state-space `L²` norm.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The `L²` class of the time integral of a stationary state observable. -/
noncomputable def timeIntegralLp (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (g : Lp ℝ 2 μ) (t : ℝ≥0) : Lp ℝ 2 P :=
  ((time_integral_memLp_and_sq_le hP g (Lp.memLp g) t.coe_nonneg).1).toLp
    (fun η : C(ℝ, S) => ∫ u in (0 : ℝ)..t, g (η u))

/-- The norm of a time-integrated stationary observable is bounded by elapsed time times its
state-space `L²` norm. -/
theorem norm_timeIntegralLp_le (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (g : Lp ℝ 2 μ) (t : ℝ≥0) :
    ‖timeIntegralLp hP g t‖ ≤ (t : ℝ) * ‖g‖ := by
  let : IsProbabilityMeasure P := hP.probability
  have hrep : timeIntegralLp hP g t =ᵐ[P]
      fun η : C(ℝ, S) => ∫ u in (0 : ℝ)..t, g (η u) :=
    MemLp.coeFn_toLp ((time_integral_memLp_and_sq_le hP g (Lp.memLp g) t.coe_nonneg).1)
  have hnorm : ‖timeIntegralLp hP g t‖ ^ 2 =
      ∫ η, (∫ u in (0 : ℝ)..t, g (η u)) ^ 2 ∂P := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hrep] with η hη
    rw [hη]
    simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial, pow_two]
  have hg : ‖g‖ ^ 2 = ∫ x, g x ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards with x
    simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial, pow_two]
  have hb := (time_integral_memLp_and_sq_le hP g (Lp.memLp g) t.coe_nonneg).2
  rw [← hnorm, ← hg] at hb
  have hnonneg : 0 ≤ (t : ℝ) * ‖g‖ := mul_nonneg t.coe_nonneg (norm_nonneg _)
  have hsq : ‖timeIntegralLp hP g t‖ ^ 2 ≤ ((t : ℝ) * ‖g‖) ^ 2 := by nlinarith
  nlinarith [norm_nonneg (timeIntegralLp hP g t)]

end EinsteinFull.External.DFGW
