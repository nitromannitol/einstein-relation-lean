import EinsteinRelation.Correctors.HeatKernelConvolution
import EinsteinRelation.Correctors.StationaryConvolutionFubini

/-!
# Space-time integrability for heat transfer

The Fubini estimates for the actual kernels in `paper/main.tex:1018–1022`.
-/

open MeasureTheory Filter
noncomputable section
namespace EinsteinRelation.Correctors
variable {d : ℕ}

/-- The smoothed spatial kernel is jointly measurable in time and space. -/
theorem measurable_heatKernelConvolution_joint {K : Vec d → ℝ} (hK : Measurable K) :
    Measurable (fun p : ℝ × Vec d => heatKernelConvolution p.1 K p.2) := by
  have hi : Measurable (fun q : (ℝ × Vec d) × Vec d =>
      K q.2 * euclideanHeatKernel q.1.1 (q.2 - q.1.2)) :=
    (hK.comp measurable_snd).mul (measurable_euclideanHeatKernel_joint.comp
      ((measurable_fst.comp measurable_fst).prodMk
        (measurable_snd.sub (measurable_snd.comp measurable_fst))))
  exact Measurable.ite (measurable_fst (measurableSet_singleton 0))
    (hK.comp measurable_snd) hi.stronglyMeasurable.integral_prod_right'.measurable

/-- Absolute integrability and contraction of the spatial `L¹` norm of a heat-smoothed kernel. -/
theorem integrable_heatKernelConvolution {K : Vec d → ℝ} (hKi : Integrable K)
    {t : ℝ} (ht : 0 ≤ t) :
    Integrable (heatKernelConvolution t K) ∧
      (∫ y, ‖heatKernelConvolution t K y‖) ≤ ∫ x, ‖K x‖ := by
  rcases ht.eq_or_lt with rfl | ht
  · have heq : heatKernelConvolution 0 K = K := funext fun y => by simp [heatKernelConvolution]
    rw [heq]
    exact ⟨hKi, le_rfl⟩
  have hi : Integrable (fun p : Vec d × Vec d => K p.2 * euclideanHeatKernel t (p.1 - p.2)) := by
    simpa only [ContinuousLinearMap.lsmul_apply, smul_eq_mul] using!
      hKi.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ) (integrable_euclideanHeatKernel ht)
  have heq (y : Vec d) : heatKernelConvolution t K y =
      ∫ x, K x * euclideanHeatKernel t (y - x) := by
    simp only [heatKernelConvolution, if_neg ht.ne']
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      dsimp only
      rw [← euclideanHeatKernel_neg t (x - y), neg_sub]
  have hi' : Integrable (heatKernelConvolution t K) := by
    rw [funext heq]
    exact hi.integral_prod_left
  refine ⟨hi', ?_⟩
  calc
    (∫ y, ‖heatKernelConvolution t K y‖) ≤
        ∫ y, ∫ x, ‖K x * euclideanHeatKernel t (y - x)‖ := by
      apply integral_mono hi'.norm hi.integral_norm_prod_left
      intro y
      dsimp only
      rw [heq]
      exact norm_integral_le_integral_norm _
    _ = ∫ x, ∫ y, ‖K x * euclideanHeatKernel t (y - x)‖ := integral_integral_swap hi.norm
    _ = ∫ x, ‖K x‖ := by
      simp only [norm_mul, Real.norm_of_nonneg (euclideanHeatKernel_nonneg ht.le _),
        integral_const_mul, integral_sub_right_eq_self, integral_euclideanHeatKernel ht, mul_one]

/-- An integrable spatial kernel remains integrable jointly over a bounded interval of
nonnegative times and all space; the bound is `T ‖K‖₁`. -/
theorem integrable_heatKernelConvolution_spacetime {K : Vec d → ℝ}
    (hK : Measurable K) (hKi : Integrable K) (T : ℝ) :
    Integrable (fun p : ℝ × Vec d => heatKernelConvolution p.1 K p.2)
      ((volume.restrict (Set.Ioc 0 T)).prod volume) := by
  have hm := (measurable_heatKernelConvolution_joint hK).aestronglyMeasurable
    (μ := (volume.restrict (Set.Ioc 0 T)).prod volume)
  apply (integrable_prod_iff hm).2
  refine ⟨?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact (integrable_heatKernelConvolution hKi ht.1.le).1
  · apply (integrable_const (μ := volume.restrict (Set.Ioc 0 T)) (∫ x, ‖K x‖)).mono'
      hm.norm.integral_prod_right'
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    exact (integrable_heatKernelConvolution hKi ht.1.le).2

/-- Smoothing may be moved from the observable to its spatial kernel. This is an
almost-everywhere identity for the literal convolutions, with no regularity assumption on `f`. -/
theorem horizontalMollify_heatSmoothed_ae
    (Q : Measure (FieldPair d)) [SFinite Q] (hQ : IsStationary Q)
    {K : Vec d → ℝ} (hK : Measurable K) (hKi : Integrable K)
    {f : FieldPair d → ℝ} (hf : Measurable f) (hfi : Integrable f Q)
    {t : ℝ} (ht : 0 ≤ t) :
    horizontalMollify K (heatSmoothed t f) =ᵐ[Q]
      horizontalMollify (heatKernelConvolution t K) f := by
  rcases ht.eq_or_lt with rfl | ht
  · exact ae_of_all _ fun ω => by simp [heatSmoothed, heatKernelConvolution, horizontalMollify]
  have h := horizontalMollify_comp_ae Q hQ hK hKi
    (continuous_euclideanHeatKernel t).measurable (integrable_euclideanHeatKernel ht) hf hfi
  have hfun : heatSmoothed t f = horizontalMollify (euclideanHeatKernel t) f := by
    ext ω
    simp only [heatSmoothed, if_neg ht.ne', horizontalMollify]
  rw [hfun]
  have heq : (fun y => ∫ x, K x * euclideanHeatKernel t (y - x)) =
      heatKernelConvolution t K := by
    ext y
    simp only [heatKernelConvolution, if_neg ht.ne']
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      dsimp only
      rw [← euclideanHeatKernel_neg t (y - x), neg_sub]
  rwa [heq] at h

end EinsteinRelation.Correctors
