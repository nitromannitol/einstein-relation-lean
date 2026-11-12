import EinsteinRelation.Correctors.StationaryConvolutionComposition
import EinsteinRelation.Correctors.HeatKernelSpaceTime

/-! # Heat transfer on actual stationary fields

Source: `paper/main.tex:1030–1032`. The spatial heat equation and Fubini's
theorem prove the heat-transfer identity for smooth compact kernels and
measurable integrable stationary fields.
-/

open MeasureTheory

noncomputable section

namespace EinsteinRelation.Correctors

variable {d : ℕ}

/-- Joint measurability of an orbit convolution with a measurable family
of kernels (`paper/main.tex:1030–1032`). -/
theorem measurable_horizontalMollify_parameter {α : Type*} [MeasurableSpace α]
    {K : α → Vec d → ℝ} (hK : Measurable (fun q : α × Vec d => K q.1 q.2))
    {f : FieldPair d → ℝ} (hf : Measurable f) :
    Measurable (fun q : α × FieldPair d => horizontalMollify (K q.1) f q.2) := by
  have hp : Measurable (fun q : (α × FieldPair d) × Vec d => (q.1.1, q.2)) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have ht : Measurable (fun q : (α × FieldPair d) × Vec d => translate q.2 q.1.2) :=
    Probability.continuous_translate.measurable.comp
      (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
  exact ((hK.comp hp).mul (hf.comp ht)).stronglyMeasurable.integral_prod_right'.measurable

/-- The heat-transfer identity for an actual integrable stationary field
(`paper/main.tex:1030–1032`). No heat-transfer or differentiability
assumption on the field is needed. -/
theorem horizontalMollify_heatTransfer_ae {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) {K : Vec d → ℝ}
    (hK : ContDiff ℝ (⊤ : ℕ∞) K) (hKc : HasCompactSupport K)
    {f : FieldPair d → ℝ} (hf : Measurable f) (hfi : Integrable f Q)
    {T : ℝ} (hT : 0 < T) :
    horizontalMollify K f =ᵐ[Q] fun ω =>
      horizontalMollify K (heatSmoothed T f) ω -
        ∫ t in (0 : ℝ)..T, horizontalMollify (coordLaplacian K) (heatSmoothed t f) ω := by
  let J : ℝ → Vec d → ℝ := fun t x => ∫ z, coordLaplacian K z * euclideanHeatKernel t (x - z)
  let ν : Measure ℝ := volume.restrict (Set.Ioc 0 T)
  have hL : Measurable (coordLaplacian K) := (contDiff_coordLaplacian hK).continuous.measurable
  have hLi : Integrable (coordLaplacian K) volume := integrable_coordLaplacian_of_smooth hK hKc
  have hJ : Measurable (fun q : ℝ × Vec d => J q.1 q.2) := measurable_kernel_heat_joint hL
  have hi := integrable_weighted_translate hQ (ν.prod volume) hJ
    (integrable_kernel_heat_spaceTime hL hLi T) measurable_snd hf hfi
  have hc : ∀ᵐ t ∂ν, ∀ᵐ ω ∂Q, horizontalMollify (J t) f ω =
      horizontalMollify (coordLaplacian K) (heatSmoothed t f) ω := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simpa only [heatSmoothed, if_neg ht.1.ne', horizontalMollify] using
      horizontalMollify_convolution_ae hQ hL hLi
        (contDiff_euclideanHeatKernel t).continuous.measurable
        (Clock.integrable_euclideanHeatKernel ht.1) hf hfi
  have hc' : ∀ᵐ ω ∂Q, ∀ᵐ t ∂ν, horizontalMollify (J t) f ω =
      horizontalMollify (coordLaplacian K) (heatSmoothed t f) ω :=
    (Measure.ae_ae_comm (μ := ν) (ν := Q)
      (p := fun t ω => horizontalMollify (J t) f ω =
        horizontalMollify (coordLaplacian K) (heatSmoothed t f) ω)
      (measurableSet_eq_fun (measurable_horizontalMollify_parameter hJ hf)
      ((measurable_horizontalMollify_heatSmoothed_joint_swap hL hf).comp measurable_swap))).mp hc
  have hb : horizontalMollify (fun x => ∫ z, K z * euclideanHeatKernel T (x - z)) f =ᵐ[Q]
      horizontalMollify K (heatSmoothed T f) := by
    have heq : heatSmoothed T f = horizontalMollify (euclideanHeatKernel T) f := by
      funext ω
      simp only [heatSmoothed, if_neg hT.ne', horizontalMollify]
    rw [heq]
    exact horizontalMollify_convolution_ae hQ hK.continuous.measurable
        (hK.continuous.integrable_of_hasCompactSupport hKc)
        (contDiff_euclideanHeatKernel T).continuous.measurable
        (Clock.integrable_euclideanHeatKernel hT) hf hfi
  have hki := ae_integrable_kernel_translate hQ hK.continuous.measurable
    (hK.continuous.integrable_of_hasCompactSupport hKc) hf hfi
  have hbi := ae_integrable_kernel_translate hQ
    ((measurable_kernel_heat_joint hK.continuous.measurable).comp
      (measurable_const.prodMk measurable_id))
    (integrable_kernel_heat (hK.continuous.integrable_of_hasCompactSupport hKc) hT) hf hfi
  filter_upwards [hi.prod_right_ae, hc', hb, hki, hbi] with ω hω hcω hbω hkiω hbiω
  have hevol : (∫ t in (0 : ℝ)..T,
      horizontalMollify (coordLaplacian K) (heatSmoothed t f) ω) =
      horizontalMollify (fun x => ∫ z, K z * euclideanHeatKernel T (x - z)) f ω -
        horizontalMollify K f ω := by
    rw [intervalIntegral.integral_of_le hT.le]
    change (∫ t, horizontalMollify (coordLaplacian K) (heatSmoothed t f) ω ∂ν) = _
    rw [← integral_congr_ae hcω]
    change (∫ t, ∫ x, J t x * f (translate x ω) ∂volume ∂ν) = _
    rw [integral_integral_swap (f := fun t x => J t x * f (translate x ω)) hω]
    simp_rw [integral_mul_const]
    have hJint (x : Vec d) : (∫ t, J t x ∂ν) =
        (∫ z, K z * euclideanHeatKernel T (x - z)) - K x := by
      rw [← intervalIntegral.integral_of_le hT.le]
      exact integral_kernel_heat_evolution hK hKc hT x
    simp_rw [hJint, sub_mul]
    exact integral_sub hbiω hkiω
  rw [hbω] at hevol
  linarith

end EinsteinRelation.Correctors
