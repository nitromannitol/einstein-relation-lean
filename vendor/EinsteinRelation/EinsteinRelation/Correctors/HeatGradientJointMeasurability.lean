import EinsteinRelation.Correctors.HeatGradientConvolution
import EinsteinRelation.Correctors.HeatConvolutionMeasurability

/-! Source: `paper/main.tex:716,748`. Joint measurability of the literal
space-first heat-gradient integral, including its zero branch at
nonpositive times. -/
open MeasureTheory
namespace EinsteinRelation.Correctors
open HeatSelectedSkewMeaning

/-- The positive-time Gaussian Hessian formula defines a measurable
function of time and space, independently of differentiation at time zero. -/
private theorem measurable_heat_hessian_formula {d : ℕ} (i j : Fin d) :
    Measurable (fun p : ℝ × Vec d => euclideanHeatKernel p.1 p.2 *
      (p.2 i * p.2 j / (4 * p.1 ^ 2) - if i = j then 1 / (2 * p.1) else 0)) := by
  apply measurable_euclideanHeatKernel_joint.mul
  apply Measurable.sub
  · exact (((measurable_pi_apply i).comp measurable_snd).mul
      ((measurable_pi_apply j).comp measurable_snd)).div
        (measurable_const.mul (measurable_fst.pow_const 2))
  · by_cases h : i = j
    · simp only [if_pos h]
      exact measurable_const.div (measurable_const.mul measurable_fst)
    · simp only [if_neg h]
      exact measurable_const

/-- The actual source density is jointly measurable in environment,
time, observation point and convolution variable. -/
theorem measurable_heatGradientDensity_stationary {d : ℕ}
    (F : FieldPair d → Vec d) (hF : Measurable F) (j k l : Fin d) :
    Measurable (fun q : ((FieldPair d × ℝ) × Vec d) × Vec d =>
      akmHeatGradientDensity (fun y => F (translate y q.1.1.1))
        q.1.1.2 j k l q.1.2 q.2) := by
  let K (i : Fin d) (p : ℝ × Vec d) := euclideanHeatKernel p.1 p.2 *
    (p.2 i * p.2 l / (4 * p.1 ^ 2) - if i = l then 1 / (2 * p.1) else 0)
  have hK (i : Fin d) : Measurable (K i) := measurable_heat_hessian_formula i l
  have hpair : Measurable (fun q : ((FieldPair d × ℝ) × Vec d) × Vec d =>
      (q.1.1.2, q.1.2 - q.2)) := by fun_prop
  have horbit : Measurable (fun q : ((FieldPair d × ℝ) × Vec d) × Vec d =>
      F (translate q.2 q.1.1.1)) := hF.comp
    (Probability.continuous_translate.measurable.comp
      (measurable_snd.prodMk ((measurable_fst.comp measurable_fst).comp measurable_fst)))
  have hm : Measurable (fun q : ((FieldPair d × ℝ) × Vec d) × Vec d =>
      if 0 < q.1.1.2 then
        F (translate q.2 q.1.1.1) k * K j (q.1.1.2, q.1.2 - q.2) -
        F (translate q.2 q.1.1.1) j * K k (q.1.1.2, q.1.2 - q.2)
      else 0) := by
    apply Measurable.ite (measurableSet_lt measurable_const (by fun_prop))
    · exact (((measurable_pi_apply k).comp horbit).mul ((hK j).comp hpair)).sub
        (((measurable_pi_apply j).comp horbit).mul ((hK k).comp hpair))
    · exact measurable_const
  convert hm using 1
  funext q
  by_cases ht : 0 < q.1.1.2
  · rw [if_pos ht, akmHeatGradientDensity_eq_mixedHessian _ _ ht,
      coordinateDerivative_two_euclideanHeatKernel _ ht,
      coordinateDerivative_two_euclideanHeatKernel _ ht]
  · simp only [if_neg ht, akmHeatGradientDensity, dif_neg ht]

/-- The actual space-first source heat integral is jointly measurable,
with the total Bochner integral retaining its original order. -/
theorem measurable_actualHeatGradientSpaceIntegral_stationary {d : ℕ}
    (F : FieldPair d → Vec d) (hF : Measurable F) (j k l : Fin d) :
    Measurable (fun q : (FieldPair d × ℝ) × Vec d =>
      akmHeatGradientSpaceIntegral (fun y => F (translate y q.1.1))
        q.1.2 j k l q.2) := by
  exact (measurable_heatGradientDensity_stationary F hF j k l).stronglyMeasurable.integral_prod_right'.measurable

end EinsteinRelation.Correctors
