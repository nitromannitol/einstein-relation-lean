import EinsteinFull.External.DFGW.TimeIntegralVariance

/-! # Double-time correlation formula

The second moment of a time integral is the double time integral of its state correlations.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- A time-integrated observable paired with a time evaluation equals the time integral of
their two-time correlations. -/
theorem integral_time_integral_mul_eval (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (g : S → ℝ) (hg : MemLp g 2 μ) (u : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    (∫ η : C(ℝ, S), (∫ v in (0 : ℝ)..t, g (η v)) * g (η u) ∂P) =
      ∫ v in (0 : ℝ)..t, ∫ η : C(ℝ, S), g (η u) * g (η v) ∂P := by
  let : IsProbabilityMeasure P := hP.probability
  let ν : Measure ℝ := volume.restrict (Set.Ioc 0 t)
  have hev : MeasurePreserving (fun η : C(ℝ, S) => η u) P μ :=
    ⟨(continuous_eval_const u).measurable, hP.marginal u⟩
  have hgu : MemLp (fun η : C(ℝ, S) => g (η u)) 2 P := hg.comp_measurePreserving hev
  have hprod := integrable_joint_trajectory_mul_eval hP (fun η => g (η u)) hgu g hg (t := t)
  have hswap : (∫ v, ∫ η : C(ℝ, S), g (η u) * g (η v) ∂P ∂ν) =
      ∫ η : C(ℝ, S), ∫ v, g (η u) * g (η v) ∂ν ∂P :=
    integral_integral_swap hprod
  have hinner (η : C(ℝ, S)) : (∫ v, g (η u) * g (η v) ∂ν) =
      (∫ v in (0 : ℝ)..t, g (η v)) * g (η u) := by
    rw [integral_const_mul]
    change g (η u) * (∫ v in Set.Ioc (0 : ℝ) t, g (η v)) = _
    rw [← intervalIntegral.integral_of_le ht, mul_comm]
  simp_rw [hinner] at hswap
  simpa only [ν, intervalIntegral.integral_of_le ht] using hswap.symm

/-- The second moment of a time integral equals the double integral of two-time
correlations. -/
theorem integral_time_integral_sq_eq_double_correlation
    (hP : Draft.IsDFGWTrajectoryProcess P μ T) (g : S → ℝ) (hg : MemLp g 2 μ)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ η : C(ℝ, S), (∫ u in (0 : ℝ)..t, g (η u)) ^ 2 ∂P) =
      ∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..t,
        ∫ η : C(ℝ, S), g (η u) * g (η v) ∂P := by
  rw [integral_time_integral_sq_eq_integral_correlation hP g hg ht]
  apply intervalIntegral.integral_congr
  intro u hu
  exact integral_time_integral_mul_eval hP g hg u ht

end EinsteinFull.External.DFGW
