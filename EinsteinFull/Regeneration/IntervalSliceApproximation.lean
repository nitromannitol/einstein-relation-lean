import EinsteinFull.Regeneration.SlabSubintervalIncrement

/-!
# Increments on arbitrary interval slices

Summable product approximation errors give all increments on almost every
interval slice over an arbitrary finite transverse measure.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace EinsteinFull.Regeneration

/-- Summable product errors vanish on almost every interval slice. -/
theorem ae_tendsto_interval_slice_sq_of_summable {Z : Type*} [MeasurableSpace Z]
    (ν : Measure Z) [IsFiniteMeasure ν] (a b : ℝ) (f : ℕ → ℝ × Z → ℝ)
    (hf : ∀ n, MemLp (f n) 2 ((volume.restrict (Ioc a b)).prod ν))
    (hsum : Summable fun n => ∫ p, (f n p) ^ 2 ∂((volume.restrict (Ioc a b)).prod ν)) :
    ∀ᵐ z ∂ν, Tendsto (fun n => ∫ t in Ioc a b, (f n (t, z)) ^ 2)
      atTop (𝓝 0) := by
  let E : ℕ → Z → ℝ := fun n z => ∫ t in Ioc a b, (f n (t, z)) ^ 2
  have hE : ∀ n, Integrable (E n) ν := fun n => (hf n).integrable_sq.integral_prod_right
  have hIntegral (n : ℕ) :
      (∫ z, ‖E n z‖ ∂ν) = ∫ p, (f n p) ^ 2 ∂((volume.restrict (Ioc a b)).prod ν) := by
    have hnonneg (z : Z) : 0 ≤ E n z := integral_nonneg fun _ => sq_nonneg _
    rw [show (fun z => ‖E n z‖) = E n by
      funext z
      rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg z)]]
    exact (integral_prod_symm _ (hf n).integrable_sq).symm
  have hs : Summable fun n => ∫ z, ‖E n z‖ ∂ν := by
    simpa only [hIntegral] using hsum
  filter_upwards [PDE.ae_summable_of_summable_integral_norm hE hs] with z hz
  exact hz.tendsto_atTop_zero

/-- Dyadically summable product errors vanish on almost every closed line segment. -/
theorem ae_tendsto_interval_slice_sq_of_summable_dyadic {Z : Type*} [MeasurableSpace Z]
    (ν : Measure Z) [IsFiniteMeasure ν] (a b : ℝ) (f : ℕ → ℝ × Z → ℝ)
    (hf : ∀ n, MemLp (f n) 2 ((volume.restrict (Ioc a b)).prod ν))
    (hsum : Summable fun n => (2 : ℝ) ^ n *
      ∫ p, (f n p) ^ 2 ∂((volume.restrict (Ioc a b)).prod ν)) :
    ∀ᵐ z ∂ν, Tendsto (fun n => ∫ t in Icc a b, (f n (t, z)) ^ 2)
      atTop (𝓝 0) := by
  have hs : Summable fun n => ∫ p, (f n p) ^ 2 ∂((volume.restrict (Ioc a b)).prod ν) := by
    refine Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => sq_nonneg _) ?_ hsum
    intro n
    calc
      (∫ p, (f n p) ^ 2 ∂((volume.restrict (Ioc a b)).prod ν)) =
          1 * ∫ p, (f n p) ^ 2 ∂((volume.restrict (Ioc a b)).prod ν) := by ring
      _ ≤ (2 : ℝ) ^ n *
          ∫ p, (f n p) ^ 2 ∂((volume.restrict (Ioc a b)).prod ν) :=
        mul_le_mul_of_nonneg_right (one_le_pow₀ (by norm_num))
          (integral_nonneg fun _ => sq_nonneg _)
  filter_upwards [ae_tendsto_interval_slice_sq_of_summable ν a b f hf hs] with z hz
  simpa only [integral_Icc_eq_integral_Ioc] using hz


/-- Product square-integrability gives square-integrable interval slices. -/
theorem memLp_interval_slice_ae {Z : Type*} [MeasurableSpace Z]
    (ν : Measure Z) [IsFiniteMeasure ν] (a b : ℝ) (f : ℝ × Z → ℝ)
    (hf : MemLp f 2 ((volume.restrict (Ioc a b)).prod ν)) :
    ∀ᵐ z ∂ν, MemLp (fun t => f (t, z)) 2 (volume.restrict (Ioc a b)) := by
  have hmeas := hf.aestronglyMeasurable.prodMk_right
  have hint := hf.integrable_sq
  filter_upwards [hmeas, hint.prod_left_ae] with z hzmeas hzint
  exact (memLp_two_iff_integrable_sq hzmeas).2 hzint


/-- Smooth product approximation determines every increment on almost every interval slice. -/
theorem ae_interval_subinterval_increment_of_smooth_approximations
    {Z : Type*} [MeasurableSpace Z] (ν : Measure Z) [IsFiniteMeasure ν]
    {d : ℕ} (i : Fin d) (a b : ℝ) (hab : a < b)
    (F : ℕ → ℝ × Z → ℝ) (u g : ℝ × Z → ℝ) (E : ℕ → ℝ × Z → PDE.Vec d)
    (hF : ∀ z n, ContDiff ℝ 1 (fun t => F n (t, z)))
    (hcont : ∀ᵐ z ∂ν, ContinuousOn (fun t => u (t, z)) (Icc a b))
    (hu : MemLp u 2 ((volume.restrict (Ioc a b)).prod ν))
    (hg : MemLp g 2 ((volume.restrict (Ioc a b)).prod ν))
    (hValueLp : ∀ n, MemLp (fun p => F n p - u p) 2
      ((volume.restrict (Ioc a b)).prod ν))
    (hVectorLp : ∀ n, MemLp (fun p => PDE.vecEuclideanNorm (E n p)) 2
      ((volume.restrict (Ioc a b)).prod ν))
    (hValueSum : Summable fun n => (2 : ℝ) ^ n *
      ∫ p, (F n p - u p) ^ 2 ∂((volume.restrict (Ioc a b)).prod ν))
    (hVectorSum : Summable fun n => (2 : ℝ) ^ n *
      ∫ p, (PDE.vecEuclideanNorm (E n p)) ^ 2 ∂((volume.restrict (Ioc a b)).prod ν))
    (hDerivative : ∀ z n t, deriv (fun r => F n (r, z)) t - g (t, z) = E n (t, z) i) :
    ∀ᵐ z ∂ν, ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      u (t, z) - u (s, z) = ∫ x in s..t, g (x, z) := by
  have humeas := memLp_interval_slice_ae ν a b u hu
  have hgmeas := memLp_interval_slice_ae ν a b g hg
  have hvmeas := ae_all_iff.2 (fun n => memLp_interval_slice_ae ν a b (fun p => F n p - u p)
    (hValueLp n))
  have hemeas := ae_all_iff.2 (fun n => memLp_interval_slice_ae ν a b
    (fun p => PDE.vecEuclideanNorm (E n p)) (hVectorLp n))
  have hvlim := ae_tendsto_interval_slice_sq_of_summable_dyadic ν a b
    (fun n p => F n p - u p) hValueLp hValueSum
  have helim := ae_tendsto_interval_slice_sq_of_summable_dyadic ν a b
    (fun n p => PDE.vecEuclideanNorm (E n p)) hVectorLp hVectorSum
  filter_upwards [hcont, humeas, hgmeas, hvmeas, hemeas, hvlim, helim] with
    z hc hu' hg' hv' he' hvlim' helim'
  have hu'' : MemLp (fun t => u (t, z)) 2 (volume.restrict (Icc a b)) := by
    rwa [← Measure.restrict_congr_set Ioc_ae_eq_Icc]
  have hg'' : MemLp (fun t => g (t, z)) 2 (volume.restrict (Icc a b)) := by
    rwa [← Measure.restrict_congr_set Ioc_ae_eq_Icc]
  have hv'' (n : ℕ) : MemLp (fun t => F n (t, z) - u (t, z)) 2
      (volume.restrict (Icc a b)) := by
    rw [← Measure.restrict_congr_set Ioc_ae_eq_Icc]
    exact hv' n
  have he'' (n : ℕ) : MemLp (fun t => PDE.vecEuclideanNorm (E n (t, z))) 2
      (volume.restrict (Icc a b)) := by
    rw [← Measure.restrict_congr_set Ioc_ae_eq_Icc]
    exact he' n
  exact continuous_subinterval_increment_of_smooth_vector_errors hab (hF z) hc hu'' hg'' hv'' he''
    (by simpa only [sq_abs] using hvlim') helim' (hDerivative z)


end EinsteinFull.Regeneration
