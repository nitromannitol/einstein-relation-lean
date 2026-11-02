import EinsteinRelation.Correctors.StationaryKernelConvolution
import EinsteinRelation.Correctors.HeatSmoothing

/-! # Joint measurability for heat transfer

Source: `paper/main.tex:1020–1031`. The time-dependent convolutions in the
heat-transfer identity are measurable jointly in time and environment.
-/

open MeasureTheory

noncomputable section

namespace EinsteinRelation.Correctors

variable {d : ℕ}

/-- Joint measurability of the explicit Gaussian kernel
(`paper/main.tex:1020–1022`). -/
theorem measurable_euclideanHeatKernel_joint :
    Measurable (fun q : ℝ × Vec d => euclideanHeatKernel q.1 q.2) := by
  have hsq : Measurable (fun q : ℝ × Vec d => euclideanSq q.2) := by
    unfold euclideanSq dot
    exact Finset.measurable_sum _ fun i _ =>
      ((measurable_pi_apply i).comp measurable_snd).mul
        ((measurable_pi_apply i).comp measurable_snd)
  unfold euclideanHeatKernel
  exact ((measurable_const.mul measurable_fst).pow_const _).mul
    (Real.continuous_exp.measurable.comp (hsq.neg.div (measurable_const.mul measurable_fst)))

/-- The actual heat smoothing, including its value at time zero, is jointly
measurable (`paper/main.tex:1020–1031`). -/
theorem measurable_heatSmoothed_joint {f : FieldPair d → ℝ} (hf : Measurable f) :
    Measurable (fun q : ℝ × FieldPair d => heatSmoothed q.1 f q.2) := by
  have hpair : Measurable (fun q : (ℝ × FieldPair d) × Vec d =>
      (q.1.1, q.2)) := (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have ht : Measurable (fun q : (ℝ × FieldPair d) × Vec d => translate q.2 q.1.2) :=
    Probability.continuous_translate.measurable.comp
      (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
  have hprod : Measurable (fun q : (ℝ × FieldPair d) × Vec d =>
      euclideanHeatKernel q.1.1 q.2 * f (translate q.2 q.1.2)) :=
    (measurable_euclideanHeatKernel_joint.comp hpair).mul (hf.comp ht)
  exact Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const)
    (hf.comp measurable_snd) hprod.stronglyMeasurable.integral_prod_right'.measurable

/-- Compact-kernel convolution of the heat smoothing is jointly measurable
(`paper/main.tex:1020–1031`). -/
theorem measurable_horizontalMollify_heatSmoothed_joint_swap {K : Vec d → ℝ}
    (hK : Measurable K) {f : FieldPair d → ℝ} (hf : Measurable f) :
    Measurable (fun q : FieldPair d × ℝ => horizontalMollify K (heatSmoothed q.2 f) q.1) := by
  have ht : Measurable (fun q : (FieldPair d × ℝ) × Vec d => translate q.2 q.1.1) :=
    Probability.continuous_translate.measurable.comp
      (measurable_snd.prodMk (measurable_fst.comp measurable_fst))
  have hpair : Measurable (fun q : (FieldPair d × ℝ) × Vec d =>
      (q.1.2, translate q.2 q.1.1)) := (measurable_snd.comp measurable_fst).prodMk ht
  have hprod : Measurable (fun q : (FieldPair d × ℝ) × Vec d =>
      K q.2 * heatSmoothed q.1.2 f (translate q.2 q.1.1)) :=
    (hK.comp measurable_snd).mul ((measurable_heatSmoothed_joint hf).comp hpair)
  exact hprod.stronglyMeasurable.integral_prod_right'.measurable

end EinsteinRelation.Correctors
