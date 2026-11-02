import EinsteinRelation.Correctors.HeatTransferBands
import EinsteinRelation.Correctors.HeatKernelConvolutionIntegrability

/-!
# Integrated heat identity for stationary observables

The identity in `paper/main.tex:1018–1022` for the literal horizontal convolutions.
The observable needs only measurability and integrability under the stationary law.
-/

open MeasureTheory Filter
noncomputable section
namespace EinsteinRelation.Correctors
variable {d : ℕ}

/-- Joint measurability after moving smoothing to the spatial kernel. -/
theorem measurable_horizontalMollify_heatKernelConvolution_joint
    {K : Vec d → ℝ} (hK : Measurable K) {f : FieldPair d → ℝ} (hf : Measurable f) :
    Measurable (fun p : ℝ × FieldPair d =>
      horizontalMollify (heatKernelConvolution p.1 K) f p.2) := by
  have hi : Measurable (fun q : (ℝ × FieldPair d) × Vec d =>
      heatKernelConvolution q.1.1 K q.2 * f (translate q.2 q.1.2)) :=
    ((measurable_heatKernelConvolution_joint hK).comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul
      (hf.comp (Probability.continuous_translate.measurable.comp
        (measurable_snd.prodMk (measurable_snd.comp measurable_fst))))
  exact hi.stronglyMeasurable.integral_prod_right'.measurable

/-- The integrated heat identity for an integrable stationary observable and a compact `C²`
spatial kernel (`paper/main.tex:1018–1022`). All time and spatial integrals are the actual
Bochner integrals in the definitions; no external heat-transfer input is assumed. -/
theorem horizontalMollify_heat_transfer
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {K : Vec d → ℝ} (hK : ContDiff ℝ 2 K) (hKc : HasCompactSupport K)
    {f : FieldPair d → ℝ} (hf : Measurable f) (hfi : Integrable f Q)
    {T : ℝ} (hT : 0 ≤ T) :
    horizontalMollify K f =ᵐ[Q]
      heatTransferExpression T K (coordLaplacian K) f := by
  have hKi : Integrable K := hK.continuous.integrable_of_hasCompactSupport hKc
  have hLi : Integrable (coordLaplacian K) := integrable_coordLaplacian hK hKc
  have hLm : Measurable (coordLaplacian K) := (continuous_coordLaplacian hK).measurable
  let ν : Measure ℝ := volume.restrict (Set.Ioc 0 T)
  have hi0 := integrable_stationary_weight volume Q hQ hK.continuous.measurable hKi
    measurable_id hf hfi
  have hiT := integrable_stationary_weight volume Q hQ
    ((measurable_heatKernelConvolution_joint hK.continuous.measurable).comp
      (measurable_const.prodMk measurable_id))
    (integrable_heatKernelConvolution hKi hT).1 measurable_id hf hfi
  have hiTime := integrable_stationary_weight (ν.prod (volume : Measure (Vec d))) Q hQ
    (measurable_heatKernelConvolution_joint hLm)
    (integrable_heatKernelConvolution_spacetime hLm hLi T) measurable_snd hf hfi
  have hmoveT := horizontalMollify_heatSmoothed_ae Q hQ hK.continuous.measurable hKi hf hfi hT
  have hmoveTime : ∀ᵐ ω ∂Q, ∀ᵐ t ∂ν,
      horizontalMollify (coordLaplacian K) (heatSmoothed t f) ω =
        horizontalMollify (heatKernelConvolution t (coordLaplacian K)) f ω := by
    apply (Measure.ae_ae_comm (μ := ν) (ν := Q) (measurableSet_eq_fun
      (measurable_horizontalMollify_heatSmoothed_joint hLm hf)
      (measurable_horizontalMollify_heatKernelConvolution_joint hLm hf))).mp
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact horizontalMollify_heatSmoothed_ae Q hQ hLm hLi hf hfi ht.1.le
  filter_upwards [hi0.prod_left_ae, hiT.prod_left_ae, hiTime.prod_left_ae,
    hmoveT, hmoveTime] with ω hω0 hωT hωTime hωmoveT hωmoveTime
  change Integrable (fun y => K y * f (translate y ω)) at hω0
  change Integrable (fun y => heatKernelConvolution T K y * f (translate y ω)) at hωT
  have htime : Integrable (fun p : ℝ × Vec d =>
      heatKernelConvolution p.1 (coordLaplacian K) p.2 * f (translate p.2 ω))
      (ν.prod volume) := hωTime
  have hdiff : horizontalMollify (heatKernelConvolution T K) f ω - horizontalMollify K f ω =
      ∫ t, horizontalMollify (heatKernelConvolution t (coordLaplacian K)) f ω ∂ν := by
    unfold horizontalMollify
    calc
      (∫ y, heatKernelConvolution T K y * f (translate y ω)) -
          (∫ y, K y * f (translate y ω)) =
          ∫ y, (heatKernelConvolution T K y - K y) * f (translate y ω) := by
        rw [← integral_sub hωT hω0]
        apply integral_congr_ae
        exact ae_of_all _ fun y => by dsimp only; ring
      _ = ∫ y, (∫ t, heatKernelConvolution t (coordLaplacian K) y ∂ν) *
          f (translate y ω) := by
        apply integral_congr_ae
        exact ae_of_all _ fun y => by
          dsimp only
          rw [heatKernelConvolution_sub_initial hK hKc y hT,
            intervalIntegral.integral_of_le hT]
      _ = ∫ y, ∫ t, heatKernelConvolution t (coordLaplacian K) y *
          f (translate y ω) ∂ν := by simp only [integral_mul_const]
      _ = ∫ t, (∫ y, heatKernelConvolution t (coordLaplacian K) y *
          f (translate y ω)) ∂ν := integral_integral_swap htime.swap
  have htimeeq : (∫ t in (0 : ℝ)..T,
      horizontalMollify (coordLaplacian K) (heatSmoothed t f) ω) =
      ∫ t, horizontalMollify (heatKernelConvolution t (coordLaplacian K)) f ω ∂ν := by
    rw [intervalIntegral.integral_of_le hT]
    exact integral_congr_ae hωmoveTime
  change horizontalMollify K f ω = horizontalMollify K (heatSmoothed T f) ω - _
  rw [hωmoveT, htimeeq, ← hdiff]
  ring

end EinsteinRelation.Correctors
