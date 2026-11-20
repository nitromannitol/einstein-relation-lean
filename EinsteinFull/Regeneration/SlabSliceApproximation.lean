import EinsteinFull.Regeneration.SlabSliceEnergy
import PDEFoundation.Measure.CommonSquareRadius
import PDEFoundation.Sobolev.Trace.VectorErrorLimit

/-!
# Square-integrable errors on slab slices

Summable product-space approximation errors vanish on almost every
force-coordinate slice.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace EinsteinFull.Regeneration

/-- Summable `L²` product errors vanish in `L²` on almost every line. -/
theorem ae_tendsto_slab_slice_sq_of_summable {Z : Type*} [MeasurableSpace Z]
    (ν : Measure Z) [IsFiniteMeasure ν] (L : ℝ) (f : ℕ → ℝ × Z → ℝ)
    (hf : ∀ n, MemLp (f n) 2 ((volume.restrict (Ioc 0 L)).prod ν))
    (hsum : Summable fun n => ∫ p, (f n p) ^ 2 ∂((volume.restrict (Ioc 0 L)).prod ν)) :
    ∀ᵐ z ∂ν, Tendsto (fun n => ∫ t in Ioc 0 L, (f n (t, z)) ^ 2)
      atTop (𝓝 0) := by
  let E : ℕ → Z → ℝ := fun n z => ∫ t in Ioc 0 L, (f n (t, z)) ^ 2
  have hE : ∀ n, Integrable (E n) ν := fun n => (hf n).integrable_sq.integral_prod_right
  have hIntegral (n : ℕ) :
      (∫ z, ‖E n z‖ ∂ν) = ∫ p, (f n p) ^ 2 ∂((volume.restrict (Ioc 0 L)).prod ν) := by
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
theorem ae_tendsto_slab_slice_sq_of_summable_dyadic {Z : Type*} [MeasurableSpace Z]
    (ν : Measure Z) [IsFiniteMeasure ν] (L : ℝ) (f : ℕ → ℝ × Z → ℝ)
    (hf : ∀ n, MemLp (f n) 2 ((volume.restrict (Ioc 0 L)).prod ν))
    (hsum : Summable fun n => (2 : ℝ) ^ n *
      ∫ p, (f n p) ^ 2 ∂((volume.restrict (Ioc 0 L)).prod ν)) :
    ∀ᵐ z ∂ν, Tendsto (fun n => ∫ t in Icc 0 L, (f n (t, z)) ^ 2)
      atTop (𝓝 0) := by
  have hs : Summable fun n => ∫ p, (f n p) ^ 2 ∂((volume.restrict (Ioc 0 L)).prod ν) := by
    refine Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => sq_nonneg _) ?_ hsum
    intro n
    calc
      (∫ p, (f n p) ^ 2 ∂((volume.restrict (Ioc 0 L)).prod ν)) =
          1 * ∫ p, (f n p) ^ 2 ∂((volume.restrict (Ioc 0 L)).prod ν) := by ring
      _ ≤ (2 : ℝ) ^ n *
          ∫ p, (f n p) ^ 2 ∂((volume.restrict (Ioc 0 L)).prod ν) :=
        mul_le_mul_of_nonneg_right (one_le_pow₀ (by norm_num))
          (integral_nonneg fun _ => sq_nonneg _)
  filter_upwards [ae_tendsto_slab_slice_sq_of_summable ν L f hf hs] with z hz
  simpa only [integral_Icc_eq_integral_Ioc] using hz

/-- A continuous representative has the exact increment of its smooth `L²` approximants. -/
theorem continuous_increment_of_smooth_vector_errors
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
    u b - u a = ∫ t in a..b, g t := by
  obtain ⟨_, hlimcont, hlim, hweak⟩ :=
    PDE.uniformCauchySeqLimit_hasWeakDerivOnIoo_of_tendsto_setIntegral_sq_vector_error
      hab hF hu hg hValueError hVectorError hValue hVector hDerivativeError
  have heq := Measure.eqOn_Icc_of_ae_eq volume hab.ne hlim hlimcont hcont
  have hlimLp : MemLp (PDE.uniformCauchySeqLimit F) 2 (volume.restrict (Ioo a b)) := by
    rw [Measure.restrict_congr_set Ioo_ae_eq_Icc]
    exact hu.ae_eq hlim.symm
  have hinc := PDE.ContinuousOn.increment_eq_intervalIntegral_of_hasWeakDerivOnIoo
    hab hlimcont hlimLp hg hweak (s := a) (t := b) (by simp [hab.le]) (by simp [hab.le])
  simpa only [heq (right_mem_Icc.mpr hab.le), heq (left_mem_Icc.mpr hab.le)] using hinc

end EinsteinFull.Regeneration
