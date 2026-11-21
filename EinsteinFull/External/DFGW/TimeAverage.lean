import EinsteinFull.External.DFGW.JointIntegrability

/-! # Expectations of time-integrated observables

The expectation of the time integral of an integrable stationary observable is the interval
length times its stationary expectation.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- A stationary observable has an integrable time average, with its expected value given by
stationary expectation times elapsed time. -/
theorem integral_time_observable (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (g : S → ℝ) (hg : Integrable g μ) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun η : C(ℝ, S) => ∫ u in (0 : ℝ)..t, g (η u)) P ∧
      (∫ η : C(ℝ, S), (∫ u in (0 : ℝ)..t, g (η u)) ∂P) =
        t * ∫ x, g x ∂μ := by
  let : IsProbabilityMeasure P := hP.probability
  let ν : Measure ℝ := volume.restrict (Set.Ioc 0 t)
  have hprod := integrable_joint_observable hP g hg 0 t
  have hi : Integrable (fun η : C(ℝ, S) => ∫ u, g (η u) ∂ν) P :=
    hprod.integral_prod_right
  constructor
  · simpa only [intervalIntegral.integral_of_le ht] using hi
  · have hswap : (∫ u, ∫ η : C(ℝ, S), g (η u) ∂P ∂ν) =
        ∫ η : C(ℝ, S), ∫ u, g (η u) ∂ν ∂P :=
      integral_integral_swap hprod
    have hmap (u : ℝ) : (∫ η : C(ℝ, S), g (η u) ∂P) = ∫ x, g x ∂μ := by
      have hm : AEStronglyMeasurable g (P.map (fun η : C(ℝ, S) => η u)) := by
        rw [hP.marginal]
        exact hg.aestronglyMeasurable
      have hi := integral_map (μ := P) (continuous_eval_const u).measurable.aemeasurable hm
      rw [hP.marginal] at hi
      exact hi.symm
    simp_rw [hmap] at hswap
    rw [integral_const] at hswap
    have hν : ν.real Set.univ = t := by
      simp only [ν, measureReal_def, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero,
        ENNReal.toReal_ofReal ht]
    rw [hν, smul_eq_mul] at hswap
    simpa only [intervalIntegral.integral_of_le ht] using hswap.symm

end EinsteinFull.External.DFGW
