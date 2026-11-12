import EinsteinRelation.Correctors.HeatKernelScaling
import EinsteinRelation.Correctors.RadialBandMomentBounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Evolution of a compact spatial kernel under the heat equation

Source: `paper/main.tex:1030–1032`. Differentiating the heat convolution
of a smooth compact kernel moves the Laplacian onto that kernel. The
resulting time derivative is bounded uniformly down to time zero.
-/

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace EinsteinRelation.Correctors

variable {d : ℕ}

private theorem continuous_euclideanSq : Continuous (fun x : Vec d => euclideanSq x) := by
  change Continuous (fun x : Vec d => ∑ i, x i * x i)
  exact continuous_finset_sum _ fun i _ => (continuous_apply i).mul (continuous_apply i)

private theorem heat_continuousAt_joint (q : ℝ × Vec d) (hq : 0 < q.1) :
    ContinuousAt (fun p : ℝ × Vec d => euclideanHeatKernel p.1 p.2) q := by
  have hbase : ContinuousAt (fun p : ℝ × Vec d => 4 * Real.pi * p.1) q := by fun_prop
  have hb : 4 * Real.pi * q.1 ≠ 0 := by positivity
  unfold euclideanHeatKernel
  exact (hbase.rpow_const (Or.inl hb)).mul
    (Real.continuous_exp.continuousAt.comp
      ((continuous_euclideanSq.continuousAt.comp continuous_snd.continuousAt).neg.div
      (show ContinuousAt (fun p : ℝ × Vec d => 4 * p.1) q by fun_prop)
      (by positivity)))

private theorem heat_laplacian_continuousAt_joint (q : ℝ × Vec d) (hq : 0 < q.1) :
    ContinuousAt (fun p : ℝ × Vec d => coordLaplacian (euclideanHeatKernel p.1) p.2) q := by
  simp only [coordLaplacian_euclideanHeatKernel]
  apply (heat_continuousAt_joint q hq).mul
  apply ContinuousAt.sub
  · exact (continuous_euclideanSq.continuousAt.comp continuous_snd.continuousAt).div
      (by fun_prop) (by positivity)
  · exact continuousAt_const.div (by fun_prop) (by positivity)

private theorem euclideanHeatKernel_neg (t : ℝ) (z : Vec d) :
    euclideanHeatKernel t (-z) = euclideanHeatKernel t z := by
  have hsq : euclideanSq (-z) = euclideanSq z := by
    change (∑ i, (-z i) * (-z i)) = ∑ i, z i * z i
    simp only [neg_mul_neg]
  simp only [euclideanHeatKernel, hsq]

private theorem coordLaplacian_comp_add_left (K : Vec d → ℝ) (a z : Vec d) :
    coordLaplacian (fun y => K (a + y)) z = coordLaplacian K (a + z) := by
  simp only [coordLaplacian, fderiv_comp_add_left]
  apply Finset.sum_congr rfl
  intro i _
  change (fderiv ℝ ((fun y => fderiv ℝ K y (unitVector i)) ∘ fun y => a + y) z)
    (unitVector i) = _
  exact congrArg (fun L : Vec d →L[ℝ] ℝ => L (unitVector i))
    (fderiv_comp_add_left (f := fun y => fderiv ℝ K y (unitVector i)) a)

private theorem coordLaplacian_heat_sub (t : ℝ) (x z : Vec d) :
    coordLaplacian (fun y => euclideanHeatKernel t (x - y)) z =
      coordLaplacian (euclideanHeatKernel t) (x - z) := by
  have heq : (fun y => euclideanHeatKernel t (x - y)) =
      fun y => euclideanHeatKernel t (-x + y) := by
    funext y
    rw [← euclideanHeatKernel_neg t (x - y), neg_sub]
    congr 1
    abel
  have hlapneg : coordLaplacian (euclideanHeatKernel t) (-(x - z)) =
      coordLaplacian (euclideanHeatKernel t) (x - z) := by
    simp only [coordLaplacian_euclideanHeatKernel, euclideanHeatKernel_neg]
    have hsq : euclideanSq (-(x - z)) = euclideanSq (x - z) := by
      change (∑ i, (-(x - z) i) * (-(x - z) i)) = ∑ i, (x - z) i * (x - z) i
      simp only [neg_mul_neg]
    rw [hsq]
  rw [heq, coordLaplacian_comp_add_left]
  rw [show -x + z = -(x - z) by abel]
  exact hlapneg

/-- The derivative of the heat convolution of a compact smooth kernel
is convolution of its spatial Laplacian (`paper/main.tex:1030–1032`). -/
theorem hasDerivAt_integral_kernel_heat {K : Vec d → ℝ}
    (hK : ContDiff ℝ 2 K) (hKc : HasCompactSupport K) (x : Vec d)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => ∫ z, K z * euclideanHeatKernel s (x - z))
      (∫ z, coordLaplacian K z * euclideanHeatKernel t (x - z)) t := by
  let J : ℝ × Vec d → ℝ := fun p => coordLaplacian (euclideanHeatKernel p.1) (x - p.2)
  have hJ : ContinuousOn J (Set.Icc (t / 2) (3 * t / 2) ×ˢ tsupport K) := by
    intro p hp
    have hmap : ContinuousAt (fun q : ℝ × Vec d => (q.1, x - q.2)) p := by fun_prop
    exact ((heat_laplacian_continuousAt_joint (p.1, x - p.2) (by
      have := hp.1.1
      linarith)).comp (f := fun q : ℝ × Vec d => (q.1, x - q.2)) (x := p) hmap).continuousWithinAt
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hKc).exists_bound_of_continuousOn hJ
  have hKi : Integrable K volume := hK.continuous.integrable_of_hasCompactSupport hKc
  have hspace (s : ℝ) : Continuous (fun z : Vec d => euclideanHeatKernel s (x - z)) :=
    (contDiff_euclideanHeatKernel s).continuous.comp (continuous_const.sub continuous_id)
  have hJt : Continuous (fun z : Vec d => J (t, z)) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    have hmap : ContinuousAt (fun y : Vec d => (t, x - y)) z := by fun_prop
    exact (heat_laplacian_continuousAt_joint (t, x - z) ht).comp
      (f := fun y : Vec d => (t, x - y)) (x := z) hmap
  have hbound : ∀ᵐ z ∂(volume : Measure (Vec d)), ∀ s ∈ Metric.ball t (t / 2),
      ‖K z * J (s, z)‖ ≤ ‖K z‖ * max C 0 := by
    refine ae_of_all _ fun z s hs => ?_
    rw [norm_mul]
    by_cases hz : z ∈ tsupport K
    · apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply (hC (s, z) ⟨?_, hz⟩).trans (le_max_left _ _)
      rw [Metric.mem_ball, Real.dist_eq] at hs
      constructor <;> linarith [neg_abs_le (s - t), le_abs_self (s - t)]
    · have hzero : K z = 0 := image_eq_zero_of_notMem_tsupport hz
      simp only [hzero, norm_zero, zero_mul, le_refl]
  have hdiff : ∀ᵐ z ∂(volume : Measure (Vec d)), ∀ s ∈ Metric.ball t (t / 2),
      HasDerivAt (fun v => K z * euclideanHeatKernel v (x - z)) (K z * J (s, z)) s := by
    refine ae_of_all _ fun z s hs => ?_
    have hspos : 0 < s := by
      rw [Metric.mem_ball, Real.dist_eq] at hs
      linarith [neg_abs_le (s - t)]
    exact (hasDerivAt_euclideanHeatKernel_heat (x - z) hspos).const_mul (K z)
  have hder := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s z => K z * euclideanHeatKernel s (x - z))
    (F' := fun s z => K z * J (s, z)) (bound := fun z => ‖K z‖ * max C 0)
    (show 0 < t / 2 by linarith)
    (Eventually.of_forall fun s => (hK.continuous.mul (hspace s)).aestronglyMeasurable)
    (integrable_mul_of_compact_support hK.continuous hKc (hspace t))
    (hK.continuous.mul hJt).aestronglyMeasurable hbound
    (hKi.norm.mul_const (max C 0)) hdiff).2
  have hp2 : ContDiff ℝ 2 (euclideanHeatKernel (d := d) t) :=
    (contDiff_euclideanHeatKernel t).of_le (by norm_cast)
  have hφ : ContDiff ℝ 2 (fun z : Vec d => euclideanHeatKernel t (x - z)) :=
    hp2.comp (contDiff_const.sub contDiff_id)
  have hibp := integral_mul_coordLaplacian_eq hK hKc hφ
  simp_rw [coordLaplacian_heat_sub] at hibp
  rw [← hibp]
  exact hder

/-- Convolution with the positive, normalized heat kernel preserves a
uniform scalar bound (`paper/main.tex:1030–1032`). -/
theorem norm_integral_kernel_heat_le {K : Vec d → ℝ} {C : ℝ}
    (hK : ∀ z, ‖K z‖ ≤ C) {t : ℝ} (ht : 0 < t) (x : Vec d) :
    ‖∫ z, K z * euclideanHeatKernel t (x - z)‖ ≤ C := by
  have hpi : Integrable (fun z : Vec d => euclideanHeatKernel t (x - z)) volume :=
    (Clock.integrable_euclideanHeatKernel ht).comp_sub_left x
  have h := norm_integral_le_of_norm_le
    (f := fun z : Vec d => K z * euclideanHeatKernel t (x - z))
    (hpi.mul_const C) (ae_of_all _ fun z => by
    rw [norm_mul, Real.norm_of_nonneg (Clock.euclideanHeatKernel_nonneg ht _)]
    exact (mul_le_mul_of_nonneg_right (hK z) (Clock.euclideanHeatKernel_nonneg ht _)).trans_eq
      (mul_comm _ _))
  simpa only [integral_mul_const, integral_sub_left_eq_self,
    Clock.integral_euclideanHeatKernel ht, one_mul] using h

/-- The time-integrated heat equation for an actual compact smooth
spatial kernel, including its initial value (`paper/main.tex:1030–1032`). -/
theorem integral_kernel_heat_evolution {K : Vec d → ℝ}
    (hK : ContDiff ℝ (⊤ : ℕ∞) K) (hKc : HasCompactSupport K)
    {T : ℝ} (hT : 0 < T) (x : Vec d) :
    (∫ t in (0 : ℝ)..T, ∫ z, coordLaplacian K z * euclideanHeatKernel t (x - z)) =
      (∫ z, K z * euclideanHeatKernel T (x - z)) - K x := by
  have hK2 : ContDiff ℝ 2 K := hK.of_le (by norm_cast)
  choose C hC using fun i : Fin d =>
    ((hKc.fderiv_apply ℝ (unitVector i)).fderiv_apply ℝ (unitVector i)).exists_bound_of_continuous
      (KernelCalculus.contDiff_coordinateIterate hK [i, i]).continuous
  have hbound (z : Vec d) : ‖coordLaplacian K z‖ ≤ ∑ i, C i := by
    apply (norm_sum_le _ _).trans
    exact Finset.sum_le_sum fun i _ => hC i z
  have hpair : Measurable (fun p : ℝ × Vec d => (p.1, x - p.2)) :=
    measurable_fst.prodMk (measurable_const.sub measurable_snd)
  have hmeas : Measurable (fun t : ℝ =>
      ∫ z, coordLaplacian K z * euclideanHeatKernel t (x - z)) :=
    (((contDiff_coordLaplacian hK).continuous.measurable.comp measurable_snd).mul
      (measurable_euclideanHeatKernel_joint.comp hpair)).stronglyMeasurable.integral_prod_right'.measurable
  have hi : IntervalIntegrable (fun t : ℝ =>
      ∫ z, coordLaplacian K z * euclideanHeatKernel t (x - z)) volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le]
    apply IntegrableOn.of_bound (by simp) hmeas.aestronglyMeasurable (∑ i, C i)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact norm_integral_kernel_heat_le hbound ht.1 x
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hT
    (fun t ht => hasDerivAt_integral_kernel_heat hK2 hKc x ht.1) hi
    (tendsto_integral_kernel_heat_zero hK.continuous hKc x)
    ((hasDerivAt_integral_kernel_heat hK2 hKc x hT).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds)

end EinsteinRelation.Correctors
