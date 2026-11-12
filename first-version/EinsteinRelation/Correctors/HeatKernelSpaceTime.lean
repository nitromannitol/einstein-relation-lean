import EinsteinRelation.Correctors.HeatKernelEvolution

/-! # Space-time integrability of heat-evolved kernels

Source: `paper/main.tex:1030–1032`. The heat evolution of an integrable
spatial kernel has uniformly bounded spatial `L¹` mass. This justifies
integrating the evolution identity against stationary fields.
-/

open MeasureTheory

noncomputable section

namespace EinsteinRelation.Correctors

variable {d : ℕ}

private theorem integrable_heat_convolution_integrand {K : Vec d → ℝ}
    (hKi : Integrable K volume) {t : ℝ} (ht : 0 < t) :
    Integrable (fun q : Vec d × Vec d => K q.1 * euclideanHeatKernel t (q.2 - q.1))
      (volume.prod volume) := by
  exact (measurePreserving_prod_sub (volume : Measure (Vec d)) volume).integrable_comp_of_integrable
    (hKi.mul_prod (Clock.integrable_euclideanHeatKernel ht))

/-- Heat evolution preserves integrability of a spatial kernel
(`paper/main.tex:1030–1032`). -/
theorem integrable_kernel_heat {K : Vec d → ℝ}
    (hKi : Integrable K volume) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x => ∫ z, K z * euclideanHeatKernel t (x - z)) volume :=
  (integrable_heat_convolution_integrand hKi ht).integral_prod_right

/-- Spatial `L¹` contraction for the heat-evolved kernel
(`paper/main.tex:1030–1032`). -/
theorem integral_norm_kernel_heat_le {K : Vec d → ℝ}
    (hKi : Integrable K volume) {t : ℝ} (ht : 0 < t) :
    (∫ x, ‖∫ z, K z * euclideanHeatKernel t (x - z)‖) ≤ ∫ z, ‖K z‖ := by
  have hi := integrable_heat_convolution_integrand hKi ht
  calc
    _ ≤ ∫ x, ∫ z, ‖K z * euclideanHeatKernel t (x - z)‖ :=
      integral_mono (integrable_kernel_heat hKi ht).norm hi.integral_norm_prod_right
        (fun x => norm_integral_le_integral_norm _)
    _ = ∫ z, ∫ x, ‖K z * euclideanHeatKernel t (x - z)‖ :=
      (integral_integral_swap (f := fun z x => ‖K z * euclideanHeatKernel t (x - z)‖) hi.norm).symm
    _ = ∫ z, ‖K z‖ := by
      simp_rw [norm_mul, Real.norm_of_nonneg (Clock.euclideanHeatKernel_nonneg ht _),
        integral_const_mul, integral_sub_right_eq_self,
        Clock.integral_euclideanHeatKernel ht, mul_one]

/-- Joint measurability of the spatially evolved kernel
(`paper/main.tex:1030–1032`). -/
theorem measurable_kernel_heat_joint {K : Vec d → ℝ} (hK : Measurable K) :
    Measurable (fun q : ℝ × Vec d => ∫ z, K z * euclideanHeatKernel q.1 (q.2 - z)) := by
  have hp : Measurable (fun q : (ℝ × Vec d) × Vec d => (q.1.1, q.1.2 - q.2)) :=
    (measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).sub measurable_snd)
  exact ((hK.comp measurable_snd).mul (measurable_euclideanHeatKernel_joint.comp hp)).stronglyMeasurable.integral_prod_right'.measurable

/-- Integrability of the heat-evolved kernel over every bounded positive
time interval (`paper/main.tex:1030–1032`). -/
theorem integrable_kernel_heat_spaceTime {K : Vec d → ℝ}
    (hK : Measurable K) (hKi : Integrable K volume) (T : ℝ) :
    Integrable (fun q : ℝ × Vec d => ∫ z, K z * euclideanHeatKernel q.1 (q.2 - z))
      ((volume.restrict (Set.Ioc 0 T)).prod volume) := by
  rw [integrable_prod_iff (measurable_kernel_heat_joint hK).aestronglyMeasurable]
  refine ⟨?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact integrable_kernel_heat hKi ht.1
  · apply (integrable_const (∫ z, ‖K z‖)).mono' ?_ ?_
    · exact (measurable_kernel_heat_joint hK).stronglyMeasurable.norm.integral_prod_right'.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact integral_norm_kernel_heat_le hKi ht.1

end EinsteinRelation.Correctors
