import EinsteinRelation.Correctors.TimeIntegralLpBound
import EinsteinRelation.Correctors.FlowTimeTail

/-! # Integrating a stochastic power tail

Source: `paper/main.tex:800–808`. The estimate proves genuine product
and almost-sure time integrability in addition to the probability moment
bound. Only times in the specified tail enter its hypotheses.
-/

open MeasureTheory Set
open scoped ENNReal

namespace EinsteinRelation.Correctors

/-- A scalar moment power bound controls the actual time tail, including
its almost-sure integrability. Source: `paper/main.tex:800–808`. -/
theorem stochastic_power_tail_integrable_and_moment_le
    {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    (f : Ω × ℝ → ℝ) (hf : Measurable f)
    {C α T : ℝ} (hC : 0 < C) (hα : 0 < α) (hT : 0 < T)
    (hdecay : ∀ t : ℝ, T < t →
      eLpNorm (fun ω => f (ω,t)) p Q ≤ ENNReal.ofReal (C*t^(-1-α))) :
    Integrable f (Q.prod (volume.restrict (Ioi T))) ∧
      (∀ᵐ ω ∂Q, IntegrableOn (fun t => f (ω,t)) (Ioi T)) ∧
      eLpNorm (fun ω => ∫ t in Ioi T, f (ω,t)) p Q ≤
        ENNReal.ofReal ((C/α)*T^(-α)) := by
  let B : ℝ → ℝ := fun t => C * (max t T)^(-1-α)
  have hBm : Measurable B :=
    measurable_const.mul ((measurable_id.max measurable_const).pow_const _)
  have hBpos (t : ℝ) : 0 < B t :=
    mul_pos hC (Real.rpow_pos_of_pos (hT.trans_le (le_max_right _ _)) _)
  have hBeq : B =ᵐ[volume.restrict (Ioi T)] fun t => C*t^(-1-α) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact congrArg (fun z : ℝ => C*z^(-1-α)) (max_eq_left ht.le)
  have hBi : IntegrableOn B (Ioi T) :=
    (flow_tail_integrableOn (C := C) hα hT).congr hBeq.symm
  have hBint : (∫ t in Ioi T, B t) = (C/α)*T^(-α) :=
    (integral_congr_ae hBeq).trans (flow_tail_integral_eq hα hT)
  have hmass : 0 < ∫ t in Ioi T, B t := by
    rw [hBint]
    exact mul_pos (div_pos hC hα) (Real.rpow_pos_of_pos hT _)
  have hbound (t : ℝ) (ht : t ∈ Ioi T) :
      eLpNorm (fun ω => f (ω,t)) p Q ≤ ENNReal.ofReal (B t) := by
    have ht' : T < t := ht
    simpa only [B, max_eq_left ht'.le] using hdecay t ht'
  let f' : Ω × ℝ → ℝ := (Prod.snd ⁻¹' Ioi T).indicator f
  have hf' : Measurable f' := hf.indicator (measurableSet_Ioi.preimage measurable_snd)
  have hbound' (t : ℝ) : eLpNorm (fun ω => f' (ω,t)) p Q ≤ ENNReal.ofReal (B t) := by
    by_cases ht : T < t
    · have heq : (fun ω => f' (ω,t)) = fun ω => f (ω,t) := by
        funext ω
        exact indicator_of_mem (show (ω,t) ∈ Prod.snd ⁻¹' Ioi T from ht) f
      rw [heq]
      exact hbound t ht
    · have heq : (fun ω => f' (ω,t)) = 0 := by
        funext ω
        exact indicator_of_notMem (show (ω,t) ∉ Prod.snd ⁻¹' Ioi T from ht) f
      rw [heq, eLpNorm_zero]
      exact bot_le
  have hi' := integrable_prod_of_eLpNorm_bound (μ := Q)
    (volume.restrict (Ioi T)) hp hf' hBi (fun t => (hBpos t).le) hbound'
  have hcongr : f' =ᵐ[Q.prod (volume.restrict (Ioi T))] f := by
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae
      (ae_restrict_mem (μ := volume) measurableSet_Ioi)] with z hz
    exact indicator_of_mem (show z ∈ Prod.snd ⁻¹' Ioi T from hz) f
  have hi := hi'.congr hcongr
  refine ⟨hi, hi.prod_right_ae, ?_⟩
  have hb := eLpNorm_setIntegral_le_integral_bound volume measurableSet_Ioi hp hpt
    hf hBm hBi hBpos hmass hbound
  simpa only [hBint] using hb

end EinsteinRelation.Correctors
