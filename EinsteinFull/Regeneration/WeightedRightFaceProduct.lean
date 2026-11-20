import EinsteinFull.Regeneration.WeightedRightFace
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Weighted right-face estimate on products

Fubini transfers the one-dimensional right-face energy estimate to a slab
with an arbitrary finite transverse measure.
-/

open MeasureTheory Set PDE
open scoped ENNReal

namespace EinsteinFull.Regeneration

/-- The weighted right-face estimate holds on a product of lines. -/
theorem weighted_product_right_face_sq_le {Z : Type*} [MeasurableSpace Z]
    (ν : Measure Z) [IsFiniteMeasure ν] {a b s : ℝ} (hab : a < b) (hs : 0 ≤ s)
    (u g : ℝ × Z → ℝ)
    (hg : MemLp g 2 ((volume.restrict (Icc a b)).prod ν))
    (hvalue : Integrable (fun p => Real.exp (s * p.1) * (u (b, p.2) - u p) ^ 2)
      ((volume.restrict (Icc a b)).prod ν))
    (henergy : Integrable (fun p => Real.exp (s * p.1) * g p ^ 2)
      ((volume.restrict (Icc a b)).prod ν))
    (hslice : ∀ᵐ z ∂ν, ContinuousOn (fun x => u (x, z)) (Icc a b) ∧
      ∀ x ∈ Icc a b, u (b, z) - u (x, z) = ∫ y in x..b, g (y, z)) :
    (∫ p, Real.exp (s * p.1) * (u (b, p.2) - u p) ^ 2
      ∂((volume.restrict (Icc a b)).prod ν)) ≤
      (b - a) ^ 2 * ∫ p, Real.exp (s * p.1) * g p ^ 2
        ∂((volume.restrict (Icc a b)).prod ν) := by
  have hgmeas := hg.aestronglyMeasurable.prodMk_right
  have hgsq := hg.integrable_sq.prod_left_ae
  have hpoint : ∀ᵐ z ∂ν,
      (∫ x in Icc a b, Real.exp (s * x) * (u (b, z) - u (x, z)) ^ 2) ≤
        (b - a) ^ 2 * ∫ x in Icc a b, Real.exp (s * x) * g (x, z) ^ 2 := by
    filter_upwards [hslice, hgmeas, hgsq] with z ⟨hc, hi⟩ hm hl
    have hglp : MemLp (fun x => g (x, z)) 2 (volume.restrict (Icc a b)) :=
      (memLp_two_iff_integrable_sq hm).2 hl
    exact weighted_right_face_sq_le hab hs (fun x => u (x, z)) (fun x => g (x, z)) hc hglp hi
  have hleft := hvalue.integral_prod_right
  have hright := henergy.integral_prod_right
  calc
    (∫ p, Real.exp (s * p.1) * (u (b, p.2) - u p) ^ 2
      ∂((volume.restrict (Icc a b)).prod ν)) =
        ∫ z, (∫ x in Icc a b, Real.exp (s * x) * (u (b, z) - u (x, z)) ^ 2) ∂ν :=
      integral_prod_symm _ hvalue
    _ ≤ ∫ z, (b - a) ^ 2 * (∫ x in Icc a b, Real.exp (s * x) * g (x, z) ^ 2) ∂ν :=
      integral_mono_ae hleft (hright.const_mul _) hpoint
    _ = (b - a) ^ 2 * ∫ p, Real.exp (s * p.1) * g p ^ 2
        ∂((volume.restrict (Icc a b)).prod ν) := by
      rw [integral_const_mul, integral_prod_symm _ henergy]

end EinsteinFull.Regeneration
