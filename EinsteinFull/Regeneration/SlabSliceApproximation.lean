import EinsteinFull.Regeneration.SlabSliceEnergy
import PDEFoundation.Measure.CommonSquareRadius

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

end EinsteinFull.Regeneration
