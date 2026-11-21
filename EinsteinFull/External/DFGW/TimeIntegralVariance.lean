import EinsteinFull.External.DFGW.JointTimeProduct
import EinsteinFull.External.DFGW.TwoTimeCorrelation

/-! # Second moments of time-integrated observables

Fubini expresses the second moment of a time integral as the integral of its correlations
with point evaluations.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- A time-integral second moment is the time integral of its pointwise correlations. -/
theorem integral_time_integral_sq_eq_integral_correlation
    (hP : Draft.IsDFGWTrajectoryProcess P μ T) (g : S → ℝ) (hg : MemLp g 2 μ)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ η : C(ℝ, S), (∫ u in (0 : ℝ)..t, g (η u)) ^ 2 ∂P) =
      ∫ u in (0 : ℝ)..t, ∫ η : C(ℝ, S),
        (∫ v in (0 : ℝ)..t, g (η v)) * g (η u) ∂P := by
  let : IsProbabilityMeasure P := hP.probability
  let ν : Measure ℝ := volume.restrict (Set.Ioc 0 t)
  let A : C(ℝ, S) → ℝ := fun η => ∫ u in (0 : ℝ)..t, g (η u)
  have hprod := integrable_joint_time_integral_mul hP g g hg hg ht
  have hswap : (∫ u, ∫ η : C(ℝ, S), A η * g (η u) ∂P ∂ν) =
      ∫ η : C(ℝ, S), ∫ u, A η * g (η u) ∂ν ∂P :=
    integral_integral_swap hprod
  have hinner (η : C(ℝ, S)) : (∫ u, A η * g (η u) ∂ν) = A η ^ 2 := by
    rw [integral_const_mul]
    change A η * (∫ u in Set.Ioc (0 : ℝ) t, g (η u)) = A η ^ 2
    rw [← intervalIntegral.integral_of_le ht]
    change A η * A η = A η ^ 2
    ring
  simp_rw [hinner] at hswap
  simpa only [A, ν, intervalIntegral.integral_of_le ht] using hswap.symm

end EinsteinFull.External.DFGW
