import EinsteinFull.External.DFGW.FixedTimeProduct

/-! # Pairings with time-integrated observables

A square-integrable trajectory observable can be paired with a time-integrated stationary
observable by integrating their fixed-time pairings.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- Fubini's theorem for the pairing of an `L²` trajectory observable with a time integral. -/
theorem integral_mul_time_integral (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (A : C(ℝ, S) → ℝ) (hA : MemLp A 2 P) (g : S → ℝ) (hg : MemLp g 2 μ)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ η : C(ℝ, S), A η * (∫ u in (0 : ℝ)..t, g (η u)) ∂P) =
      ∫ u in (0 : ℝ)..t, ∫ η : C(ℝ, S), A η * g (η u) ∂P := by
  let : IsProbabilityMeasure P := hP.probability
  let ν : Measure ℝ := volume.restrict (Set.Ioc 0 t)
  have hprod := integrable_joint_trajectory_mul_eval hP A hA g hg (t := t)
  have hswap : (∫ u, ∫ η : C(ℝ, S), A η * g (η u) ∂P ∂ν) =
      ∫ η : C(ℝ, S), ∫ u, A η * g (η u) ∂ν ∂P :=
    integral_integral_swap hprod
  have hinner (η : C(ℝ, S)) : (∫ u, A η * g (η u) ∂ν) =
      A η * (∫ u in (0 : ℝ)..t, g (η u)) := by
    rw [integral_const_mul]
    change A η * (∫ u in Set.Ioc (0 : ℝ) t, g (η u)) = _
    rw [← intervalIntegral.integral_of_le ht]
  simp_rw [hinner] at hswap
  simpa only [ν, intervalIntegral.integral_of_le ht] using hswap.symm

end EinsteinFull.External.DFGW
