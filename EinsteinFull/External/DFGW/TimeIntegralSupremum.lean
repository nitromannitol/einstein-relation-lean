import EinsteinFull.External.DFGW.JointIntegrability

/-! # Uniform bounds for integrated observables

The integral of the absolute observable over an interval controls all partial time integrals.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation Filter
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The absolute integral over `[0,t]` controls all partial integrals along almost every
stationary trajectory. -/
theorem ae_abs_time_integral_le_integral_abs
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (g : S → ℝ) (hg : Integrable g μ) (t : ℝ≥0) :
    ∀ᵐ η ∂P, ∀ s : ℝ≥0, s ≤ t →
      |∫ u in (0 : ℝ)..s, g (η u)| ≤ ∫ u in (0 : ℝ)..t, |g (η u)| := by
  let : IsProbabilityMeasure P := hP.probability
  have h := (integrable_joint_observable hP g hg 0 t).prod_left_ae
  filter_upwards [h] with η hη s hst
  have ht : IntervalIntegrable (fun u => g (η u)) volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le t.coe_nonneg).2 hη
  have hs0 : (0 : ℝ) ≤ s := s.coe_nonneg
  have hst' : (s : ℝ) ≤ t := by exact_mod_cast hst
  calc
    |∫ u in (0 : ℝ)..s, g (η u)| ≤ ∫ u in (0 : ℝ)..s, |g (η u)| :=
      intervalIntegral.abs_integral_le_integral_abs hs0
    _ ≤ ∫ u in (0 : ℝ)..t, |g (η u)| :=
      intervalIntegral.integral_mono_interval le_rfl hs0 hst'
        (Eventually.of_forall fun u => abs_nonneg _) ht.abs

end EinsteinFull.External.DFGW
