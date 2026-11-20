import EinsteinFull.External.DFGW.CompensatedIncrement
import Mathlib.MeasureTheory.Integral.Prod

/-! # Joint integrability of stationary observables

An integrable observable of a stationary process is jointly integrable over a bounded time
interval and trajectory space.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S E : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable [NormedAddCommGroup E]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- An integrable observable is jointly integrable over a bounded time interval. -/
theorem integrable_joint_observable (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (φ : S → E) (hφ : Integrable φ μ) (a b : ℝ) :
    Integrable (fun z : ℝ × C(ℝ, S) => φ (z.2 z.1))
      ((volume.restrict (Set.Ioc a b)).prod P) := by
  let : IsProbabilityMeasure P := hP.probability
  let ν : Measure ℝ := volume.restrict (Set.Ioc a b)
  have hev : Measurable (fun z : ℝ × C(ℝ, S) => z.2 z.1) := by
    have hc : Continuous (fun z : C(ℝ, S) × ℝ => z.1 z.2) := continuous_eval
    exact hc.measurable.comp measurable_swap
  have hq : Measure.QuasiMeasurePreserving (fun z : ℝ × C(ℝ, S) => z.2 z.1)
      (ν.prod P) μ := by
    refine ⟨hev, Measure.AbsolutelyContinuous.mk ?_⟩
    intro A hA hAμ
    rw [Measure.map_apply hev hA, Measure.prod_apply (hev hA)]
    have hz : (fun t : ℝ => P (Prod.mk t ⁻¹' ((fun z : ℝ × C(ℝ, S) => z.2 z.1) ⁻¹' A))) = 0 := by
      funext t
      have hm := Measure.map_apply (μ := P) (continuous_eval_const t).measurable hA
      rw [hP.marginal, hAμ] at hm
      change P ((fun η : C(ℝ, S) => η t) ⁻¹' A) = 0
      exact hm.symm
    rw [hz, lintegral_zero_fun]
  have hmeas : AEStronglyMeasurable (fun z : ℝ × C(ℝ, S) => φ (z.2 z.1)) (ν.prod P) :=
    hφ.aestronglyMeasurable.comp_quasiMeasurePreserving hq
  have heach (t : ℝ) : Integrable (fun η : C(ℝ, S) => φ (η t)) P := by
    have hm : AEStronglyMeasurable φ (P.map (fun η : C(ℝ, S) => η t)) := by
      rw [hP.marginal]
      exact hφ.aestronglyMeasurable
    apply (integrable_map_measure hm (continuous_eval_const t).measurable.aemeasurable).1
    rw [hP.marginal]
    exact hφ
  have hconst (t : ℝ) : (∫ η : C(ℝ, S), ‖φ (η t)‖ ∂P) = ∫ x, ‖φ x‖ ∂μ := by
    have hm : AEStronglyMeasurable (fun x => ‖φ x‖) (P.map (fun η : C(ℝ, S) => η t)) := by
      rw [hP.marginal]
      exact hφ.norm.aestronglyMeasurable
    have hi := integral_map (μ := P) (continuous_eval_const t).measurable.aemeasurable hm
    rw [hP.marginal] at hi
    exact hi.symm
  have hprod : Integrable (fun z : ℝ × C(ℝ, S) => φ (z.2 z.1)) (ν.prod P) := by
    apply (integrable_prod_iff hmeas).2
    constructor
    · exact ae_of_all ν heach
    · simp_rw [hconst]
      exact integrable_const _
  exact hprod

end EinsteinFull.External.DFGW
