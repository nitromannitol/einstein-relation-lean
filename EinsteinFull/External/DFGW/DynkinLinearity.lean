import EinsteinFull.External.DFGW.DynkinEnergy
import EinsteinFull.External.DFGW.TimeIntegralCongruence

/-! # Linearity of Dynkin martingales

The Dynkin process is linear in its generator-domain observable, up to almost everywhere
identification of the `L²` representatives.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The Dynkin process of a difference equals the difference of the Dynkin processes almost
surely at each fixed time. -/
theorem dynkinProcess_sub_ae (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (f h : (transitionSemigroup hP).generatorDomain) (t : ℝ≥0) :
    dynkinProcess hP (f - h) t =ᵐ[P] dynkinProcess hP f t - dynkinProcess hP h t := by
  let : IsProbabilityMeasure P := hP.probability
  let : IsProbabilityMeasure μ := hP.invariant_probability
  let F : Lp ℝ 2 μ := f
  let H : Lp ℝ 2 μ := h
  let G : Lp ℝ 2 μ := (transitionSemigroup hP).generator f
  let J : Lp ℝ 2 μ := (transitionSemigroup hP).generator h
  have heval : MeasurePreserving (fun η : C(ℝ, S) => η (t : ℝ)) P μ :=
    ⟨(continuous_eval_const _).measurable, hP.marginal _⟩
  have hv : (fun η : C(ℝ, S) => ((f - h : (transitionSemigroup hP).generatorDomain) : Lp ℝ 2 μ) (η t)) =ᵐ[P]
      fun η => F (η t) - H (η t) := by
    have hs : (((f - h : (transitionSemigroup hP).generatorDomain) : Lp ℝ 2 μ) : S → ℝ) =ᵐ[μ]
        fun x => F x - H x := Lp.coeFn_sub F H
    exact heval.quasiMeasurePreserving.ae hs
  have hg : ((transitionSemigroup hP).generator (f - h) : S → ℝ) =ᵐ[μ]
      fun x => G x - J x := by
    rw [map_sub]
    exact Lp.coeFn_sub G J
  have htime := ae_time_integral_congr hP hg t.coe_nonneg
  have hG := (integrable_joint_observable hP G ((Lp.memLp G).integrable one_le_two) 0 t).prod_left_ae
  have hJ := (integrable_joint_observable hP J ((Lp.memLp J).integrable one_le_two) 0 t).prod_left_ae
  filter_upwards [hv, htime, hG, hJ] with η hvη htη hGη hJη
  have hiG := (intervalIntegrable_iff_integrableOn_Ioc_of_le t.coe_nonneg).2 hGη
  have hiJ := (intervalIntegrable_iff_integrableOn_Ioc_of_le t.coe_nonneg).2 hJη
  change ((f - h : (transitionSemigroup hP).generatorDomain) : Lp ℝ 2 μ) (η t) -
      (∫ u in (0 : ℝ)..t, (transitionSemigroup hP).generator (f - h) (η u)) =
    (F (η t) - ∫ u in (0 : ℝ)..t, G (η u)) -
      (H (η t) - ∫ u in (0 : ℝ)..t, J (η u))
  rw [hvη, htη, intervalIntegral.integral_sub hiG hiJ]
  ring

end EinsteinFull.External.DFGW
