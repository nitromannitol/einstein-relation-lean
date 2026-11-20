import PDEFoundation.Monotonicity.Core.RellichSphere
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Lower energy bounds from coordinate slices

Cauchy–Schwarz on almost every line and Fubini give the quantitative energy
lower bound in Gantert–Mathieu–Piatnitski, equation (4.12).
-/

open MeasureTheory Set
open scoped ENNReal

namespace EinsteinFull.Regeneration

/-- A one-dimensional integral bounds the squared `L²` energy. -/
theorem sq_integral_le_length_mul_integral_sq (L : ℝ) (hL : 0 ≤ L)
    (g : ℝ → ℝ) (hg : IntegrableOn g (Ioc 0 L))
    (hg2 : IntegrableOn (fun t => g t ^ 2) (Ioc 0 L)) :
    (∫ t in Ioc 0 L, g t) ^ 2 ≤ L * ∫ t in Ioc 0 L, g t ^ 2 := by
  let μ := (volume : Measure ℝ).restrict (Ioc 0 L)
  let : IsFiniteMeasure μ := by dsimp [μ]; infer_instance
  have h := PDE.integral_mul_sq_le (μ := μ) (f := fun _ : ℝ => 1) (g := g)
    (by simp) hg2
    (by simpa only [one_mul] using (show Integrable g μ from hg))
  simpa [μ, Real.volume_Ioc, max_eq_left hL] using h

/-- Uniform lower bounds on line integrals give a lower bound on total squared energy. -/
theorem slab_energy_lower_of_slice_integrals {Z : Type*} [MeasurableSpace Z]
    (ν : Measure Z) [IsFiniteMeasure ν] (L c : ℝ) (hL : 0 ≤ L) (hc : 0 ≤ c)
    (g : ℝ × Z → ℝ)
    (hg : Integrable g ((volume.restrict (Ioc 0 L)).prod ν))
    (hg2 : Integrable (fun p => g p ^ 2) ((volume.restrict (Ioc 0 L)).prod ν))
    (hbound : ∀ᵐ z ∂ν, c ≤ |∫ t in Ioc 0 L, g (t, z)|) :
    c ^ 2 * ν.real univ ≤ L * ∫ p, g p ^ 2 ∂((volume.restrict (Ioc 0 L)).prod ν) := by
  have hpoint : ∀ᵐ z ∂ν, c ^ 2 ≤ L * ∫ t in Ioc 0 L, g (t, z) ^ 2 := by
    filter_upwards [hg.prod_left_ae, hg2.prod_left_ae, hbound] with z hgi hgi2 hz
    have hcs := sq_integral_le_length_mul_integral_sq L hL (fun t => g (t, z)) hgi hgi2
    have hsq : c ^ 2 ≤ |∫ t in Ioc 0 L, g (t, z)| ^ 2 :=
      pow_le_pow_left₀ hc hz 2
    have hsq' : c ^ 2 ≤ (∫ t in Ioc 0 L, g (t, z)) ^ 2 := by
      simpa only [sq_abs] using hsq
    exact hsq'.trans hcs
  have hinner : Integrable (fun z => ∫ t in Ioc 0 L, g (t, z) ^ 2) ν := hg2.integral_prod_right
  calc
    c ^ 2 * ν.real univ = ∫ _z, c ^ 2 ∂ν := by simp [measureReal_def, mul_comm]
    _ ≤ ∫ z, L * (∫ t in Ioc 0 L, g (t, z) ^ 2) ∂ν :=
      integral_mono_ae (integrable_const _) (hinner.const_mul L) hpoint
    _ = L * ∫ p, g p ^ 2 ∂((volume.restrict (Ioc 0 L)).prod ν) := by
      rw [integral_const_mul, integral_prod_symm _ hg2]

end EinsteinFull.Regeneration
