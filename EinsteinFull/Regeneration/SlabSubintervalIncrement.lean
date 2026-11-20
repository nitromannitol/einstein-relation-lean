import EinsteinFull.Regeneration.SlabSliceApproximation

/-!
# Sobolev increments on subintervals

A single smooth approximation sequence identifies every subinterval increment
of the continuous representative on almost every slab line.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace EinsteinFull.Regeneration

/-- A smooth approximation identifies all increments of a continuous representative. -/
theorem continuous_subinterval_increment_of_smooth_vector_errors
    {d : ℕ} {i : Fin d} {a b : ℝ} (hab : a < b)
    {F : ℕ → ℝ → ℝ} {u g : ℝ → ℝ} {E : ℕ → ℝ → PDE.Vec d}
    (hF : ∀ n, ContDiff ℝ 1 (F n)) (hcont : ContinuousOn u (Icc a b))
    (hu : MemLp u 2 (volume.restrict (Icc a b)))
    (hg : MemLp g 2 (volume.restrict (Icc a b)))
    (hValueError : ∀ n, MemLp (fun t => F n t - u t) 2 (volume.restrict (Icc a b)))
    (hVectorError : ∀ n, MemLp (fun t => PDE.vecEuclideanNorm (E n t)) 2
      (volume.restrict (Icc a b)))
    (hValue : Tendsto (fun n => ∫ t in Icc a b, |F n t - u t| ^ 2) atTop (𝓝 0))
    (hVector : Tendsto (fun n => ∫ t in Icc a b, PDE.vecEuclideanNorm (E n t) ^ 2)
      atTop (𝓝 0))
    (hDerivativeError : ∀ n t, deriv (F n) t - g t = E n t i) :
    ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, u t - u s = ∫ x in s..t, g x := by
  obtain ⟨_, hlimcont, hlim, hweak⟩ :=
    PDE.uniformCauchySeqLimit_hasWeakDerivOnIoo_of_tendsto_setIntegral_sq_vector_error
      hab hF hu hg hValueError hVectorError hValue hVector hDerivativeError
  have heq := Measure.eqOn_Icc_of_ae_eq volume hab.ne hlim hlimcont hcont
  have hlimLp : MemLp (PDE.uniformCauchySeqLimit F) 2 (volume.restrict (Ioo a b)) := by
    rw [Measure.restrict_congr_set Ioo_ae_eq_Icc]
    exact hu.ae_eq hlim.symm
  intro s hs t ht
  have hinc := PDE.ContinuousOn.increment_eq_intervalIntegral_of_hasWeakDerivOnIoo
    hab hlimcont hlimLp hg hweak hs ht
  simpa only [heq ht, heq hs] using hinc

/-- Almost every slab line has the increment formula on all its subintervals. -/
theorem ae_slab_subinterval_increment_of_smooth_approximations
    {Z : Type*} [MeasurableSpace Z] (ν : Measure Z) [IsFiniteMeasure ν]
    {d : ℕ} (i : Fin d) (L : ℝ) (hL : 0 < L)
    (F : ℕ → ℝ × Z → ℝ) (u g : ℝ × Z → ℝ) (E : ℕ → ℝ × Z → PDE.Vec d)
    (hF : ∀ z n, ContDiff ℝ 1 (fun t => F n (t, z)))
    (hcont : ∀ᵐ z ∂ν, ContinuousOn (fun t => u (t, z)) (Icc 0 L))
    (hu : MemLp u 2 ((volume.restrict (Ioc 0 L)).prod ν))
    (hg : MemLp g 2 ((volume.restrict (Ioc 0 L)).prod ν))
    (hValueLp : ∀ n, MemLp (fun p => F n p - u p) 2
      ((volume.restrict (Ioc 0 L)).prod ν))
    (hVectorLp : ∀ n, MemLp (fun p => PDE.vecEuclideanNorm (E n p)) 2
      ((volume.restrict (Ioc 0 L)).prod ν))
    (hValueSum : Summable fun n => (2 : ℝ) ^ n *
      ∫ p, (F n p - u p) ^ 2 ∂((volume.restrict (Ioc 0 L)).prod ν))
    (hVectorSum : Summable fun n => (2 : ℝ) ^ n *
      ∫ p, (PDE.vecEuclideanNorm (E n p)) ^ 2 ∂((volume.restrict (Ioc 0 L)).prod ν))
    (hDerivative : ∀ z n t, deriv (fun r => F n (r, z)) t - g (t, z) = E n (t, z) i) :
    ∀ᵐ z ∂ν, ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L,
      u (t, z) - u (s, z) = ∫ x in s..t, g (x, z) := by
  have humeas := memLp_slab_slice_ae ν L u hu
  have hgmeas := memLp_slab_slice_ae ν L g hg
  have hvmeas := ae_all_iff.2 (fun n => memLp_slab_slice_ae ν L (fun p => F n p - u p)
    (hValueLp n))
  have hemeas := ae_all_iff.2 (fun n => memLp_slab_slice_ae ν L
    (fun p => PDE.vecEuclideanNorm (E n p)) (hVectorLp n))
  have hvlim := ae_tendsto_slab_slice_sq_of_summable_dyadic ν L
    (fun n p => F n p - u p) hValueLp hValueSum
  have helim := ae_tendsto_slab_slice_sq_of_summable_dyadic ν L
    (fun n p => PDE.vecEuclideanNorm (E n p)) hVectorLp hVectorSum
  filter_upwards [hcont, humeas, hgmeas, hvmeas, hemeas, hvlim, helim] with
    z hc hu' hg' hv' he' hvlim' helim'
  have hu'' : MemLp (fun t => u (t, z)) 2 (volume.restrict (Icc 0 L)) := by
    rwa [← Measure.restrict_congr_set Ioc_ae_eq_Icc]
  have hg'' : MemLp (fun t => g (t, z)) 2 (volume.restrict (Icc 0 L)) := by
    rwa [← Measure.restrict_congr_set Ioc_ae_eq_Icc]
  have hv'' (n : ℕ) : MemLp (fun t => F n (t, z) - u (t, z)) 2
      (volume.restrict (Icc 0 L)) := by
    rw [← Measure.restrict_congr_set Ioc_ae_eq_Icc]
    exact hv' n
  have he'' (n : ℕ) : MemLp (fun t => PDE.vecEuclideanNorm (E n (t, z))) 2
      (volume.restrict (Icc 0 L)) := by
    rw [← Measure.restrict_congr_set Ioc_ae_eq_Icc]
    exact he' n
  exact continuous_subinterval_increment_of_smooth_vector_errors hL (hF z) hc hu'' hg'' hv'' he''
    (by simpa only [sq_abs] using hvlim') helim' (hDerivative z)

end EinsteinFull.Regeneration
