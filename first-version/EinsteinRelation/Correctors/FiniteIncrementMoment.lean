import EinsteinRelation.Correctors.TruncatedGradientTail

/-! # Local RMS moments of zero-based gradient differences

Source: `paper/main.tex:800–808`. The energy class through zero justifies
additivity at the lower endpoint; the decay estimate controls only the
positive-time increment.
-/

open MeasureTheory Set
open scoped ENNReal
namespace EinsteinRelation.Correctors

/-- Additivity of zero-based Bochner integrals with a genuine initial
energy class. Source: `paper/main.tex:800–808`. -/
theorem initial_integral_sub
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {g : ℝ → E} {T S : ℝ} (hT : 0 ≤ T) (hTS : T ≤ S)
    (hg : IntegrableOn g (Ioo 0 S)) :
    (∫ t in Ioo 0 S, g t) - (∫ t in Ioo 0 T, g t) = ∫ t in Ioo T S, g t := by
  have hS : 0 ≤ S := hT.trans hTS
  have hiS : IntervalIntegrable g volume 0 S :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hS).mpr hg
  have hiT : IntervalIntegrable g volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hT).mpr
      (hg.mono_set (Ioo_subset_Ioo le_rfl hTS))
  simpa only [intervalIntegral.integral_of_le hS, intervalIntegral.integral_of_le hT,
    intervalIntegral.integral_of_le hTS, integral_Ioc_eq_integral_Ioo] using
      intervalIntegral.integral_interval_sub_left hiS hiT

/-- The initial space-time energy class and sharp large-time local RMS
bound give moments for differences of literal zero-based integrals.
Source: `paper/main.tex:800–808`. -/
theorem initial_gradient_increment_moment
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X] {d : ℕ}
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (ν : Measure X) [IsProbabilityMeasure ν]
    (G : Ω × (ℝ × X) → EuclideanSpace ℝ (Fin d)) (hG : Measurable G)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    {C α T S : ℝ} (hC : 0 < C) (hα : 0 < α) (hT : 0 < T) (hTS : T ≤ S)
    (hfinite : ∀ᵐ ω ∂Q, MemLp (fun z => G (ω,z)) 2
      ((volume.restrict (Ioo 0 S)).prod ν))
    (hsections : ∀ᵐ ω ∂Q, ∀ᵐ t ∂volume.restrict (Ioi T),
      MemLp (fun x => G (ω,(t,x))) 2 ν)
    (hdecay : ∀ᵐ t ∂volume.restrict (Ioi T),
      eLpNorm (fun ω => Real.sqrt (∫ x, ‖G (ω,(t,x))‖^2 ∂ν)) p Q ≤
        ENNReal.ofReal (C*t^(-1-α))) :
    (∀ᵐ ω ∂Q, MemLp (fun x =>
      (∫ t in Ioo 0 S, G (ω,(t,x))) - ∫ t in Ioo 0 T, G (ω,(t,x))) 2 ν) ∧
    eLpNorm (fun ω => Real.sqrt (∫ x,
      ‖(∫ t in Ioo 0 S, G (ω,(t,x))) - ∫ t in Ioo 0 T, G (ω,(t,x))‖^2 ∂ν)) p Q ≤
        ENNReal.ofReal ((C/α)*T^(-α)) := by
  have ht := truncated_gradient_tail_moment Q ν G hG hp hpt hC hα hT
    hsections hdecay S
  have he : ∀ᵐ ω ∂Q, ∀ᵐ x ∂ν,
      (∫ t in Ioo 0 S, G (ω,(t,x))) - (∫ t in Ioo 0 T, G (ω,(t,x))) =
        ∫ t in Ioo T S, G (ω,(t,x)) := by
    filter_upwards [hfinite] with ω hω
    filter_upwards [(hω.integrable (by norm_num)).prod_left_ae] with x hx
    exact initial_integral_sub hT.le hTS hx
  refine ⟨?_,?_⟩
  · filter_upwards [ht.1,he] with ω hω hωe
    exact MemLp.ae_eq (Filter.EventuallyEq.symm hωe) hω
  · have hrms : (fun ω => Real.sqrt (∫ x,
        ‖(∫ t in Ioo 0 S, G (ω,(t,x))) - ∫ t in Ioo 0 T, G (ω,(t,x))‖^2 ∂ν)) =ᵐ[Q]
        (fun ω => Real.sqrt (∫ x, ‖∫ t in Ioo T S, G (ω,(t,x))‖^2 ∂ν)) := by
      filter_upwards [he] with ω hω
      exact congrArg Real.sqrt (integral_congr_ae (hω.mono fun x hx => congrArg (fun v => ‖v‖^2) hx))
    rw [eLpNorm_congr_ae hrms]
    exact ht.2.2

end EinsteinRelation.Correctors
