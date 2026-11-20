import EinsteinFull.External.DFGW.FixedTimeProduct

/-! # Joint integrability for time-integrated observables

An integrated square-integrable observable times a second stationary observable is integrable
jointly in the trajectory and time variables.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The product of a time-integrated observable and a time-evaluated observable is jointly
integrable. -/
theorem integrable_joint_time_integral_mul (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (f g : S → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun z : ℝ × C(ℝ, S) =>
      (∫ u in (0 : ℝ)..t, f (z.2 u)) * g (z.2 z.1))
      ((volume.restrict (Set.Ioc 0 t)).prod P) := by
  have hA := (time_integral_memLp_and_sq_le hP f hf ht).1
  exact integrable_joint_trajectory_mul_eval hP _ hA g hg

end EinsteinFull.External.DFGW
