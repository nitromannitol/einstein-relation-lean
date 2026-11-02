import EinsteinRelation.Correctors.IntegratedHeatTransfer

/-!
# Absolute time integrability of stationary heat convolutions

The time integral in `paper/main.tex:1018–1022` is absolutely convergent
almost everywhere for any integrable stationary observable.
-/

open MeasureTheory Filter
noncomputable section
namespace EinsteinRelation.Correctors

/-- Absolute time integrability of the actual stationary heat convolutions in
`paper/main.tex:1018–1022`, without a higher moment assumption. -/
theorem ae_intervalIntegrable_horizontalMollify_heatSmoothed
    {d : ℕ} (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {L : Vec d → ℝ} (hL : Measurable L) (hLi : Integrable L)
    {f : FieldPair d → ℝ} (hf : Measurable f) (hfi : Integrable f Q)
    {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ ω ∂Q, IntervalIntegrable
      (fun t => horizontalMollify L (heatSmoothed t f) ω) volume 0 T := by
  let ν : Measure ℝ := volume.restrict (Set.Ioc 0 T)
  have hi := integrable_stationary_weight (ν.prod (volume : Measure (Vec d))) Q hQ
    (measurable_heatKernelConvolution_joint hL)
    (integrable_heatKernelConvolution_spacetime hL hLi T) measurable_snd hf hfi
  have hmove : ∀ᵐ ω ∂Q, ∀ᵐ t ∂ν,
      horizontalMollify L (heatSmoothed t f) ω =
        horizontalMollify (heatKernelConvolution t L) f ω := by
    apply (Measure.ae_ae_comm (μ := ν) (ν := Q) (measurableSet_eq_fun
      (measurable_horizontalMollify_heatSmoothed_joint hL hf)
      (measurable_horizontalMollify_heatKernelConvolution_joint hL hf))).mp
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact horizontalMollify_heatSmoothed_ae Q hQ hL hLi hf hfi ht.1.le
  filter_upwards [hi.prod_left_ae, hmove] with ω hω hωmove
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).2
  exact hω.integral_prod_left.congr (hωmove.mono fun _ ht => ht.symm)

end EinsteinRelation.Correctors
