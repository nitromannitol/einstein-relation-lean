import EinsteinFull.Regeneration.WeightedRightFaceProduct

/-!
# Left-face estimates on product slabs

The one-dimensional primitive estimate and Fubini control the squared distance
from a function to its left-face values.
-/

open MeasureTheory Set PDE
open scoped ENNReal

namespace EinsteinFull.Regeneration

/-- The left-face increment estimate on a product of lines. -/
theorem product_left_face_sq_le {Z : Type*} [MeasurableSpace Z]
    (ν : Measure Z) [IsFiniteMeasure ν] {a b : ℝ} (hab : a < b)
    (u g : ℝ × Z → ℝ)
    (hg : MemLp g 2 ((volume.restrict (Icc a b)).prod ν))
    (hvalue : Integrable (fun p => (u p - u (a, p.2)) ^ 2)
      ((volume.restrict (Icc a b)).prod ν))
    (hslice : ∀ᵐ z ∂ν, ∀ x ∈ Icc a b, u (x, z) - u (a, z) = ∫ y in a..x, g (y, z)) :
    Integrable (fun p => g p ^ 2) ((volume.restrict (Icc a b)).prod ν) ∧
    (∫ p, (u p - u (a, p.2)) ^ 2 ∂((volume.restrict (Icc a b)).prod ν)) ≤
      (b - a) ^ 2 * ∫ p, g p ^ 2 ∂((volume.restrict (Icc a b)).prod ν) := by
  have hgmeas := hg.aestronglyMeasurable.prodMk_right
  have hgsq := hg.integrable_sq.prod_left_ae
  have hpoint : ∀ᵐ z ∂ν,
      (∫ x in Icc a b, (u (x, z) - u (a, z)) ^ 2) ≤
        (b - a) ^ 2 * ∫ x in Icc a b, g (x, z) ^ 2 := by
    filter_upwards [hslice, hgmeas, hgsq] with z hi hm hl
    have hglp : MemLp (fun x => g (x, z)) 2 (volume.restrict (Icc a b)) :=
      (memLp_two_iff_integrable_sq hm).2 hl
    have hgint := hglp.integrable (by norm_num)
    have hprim := PDE.setIntegral_sq_intervalPrimitive_le_left_collar hab.le hgint hglp
    have heq : (∫ x in Icc a b, (u (x, z) - u (a, z)) ^ 2) =
        ∫ x in Icc a b, |PDE.intervalPrimitive a (fun t => g (t, z)) x| ^ 2 := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro x hx
      have h := PDE.intervalPrimitive_sub_eq_intervalIntegral hgint
        (show a ∈ Icc a b from ⟨le_rfl, hab.le⟩) hx
      rw [PDE.intervalPrimitive_self, sub_zero] at h
      rw [← hi x hx] at h
      change (u (x, z) - u (a, z)) ^ 2 =
        |PDE.intervalPrimitive a (fun t => g (t, z)) x| ^ 2
      rw [h, sq_abs]
    rw [heq]
    simpa only [Real.rpow_ofNat, sq_abs] using hprim
  refine ⟨hg.integrable_sq, ?_⟩
  have hleft := hvalue.integral_prod_right
  have hright := hg.integrable_sq.integral_prod_right
  calc
    (∫ p, (u p - u (a, p.2)) ^ 2 ∂((volume.restrict (Icc a b)).prod ν)) =
        ∫ z, (∫ x in Icc a b, (u (x, z) - u (a, z)) ^ 2) ∂ν :=
      integral_prod_symm _ hvalue
    _ ≤ ∫ z, (b - a) ^ 2 * (∫ x in Icc a b, g (x, z) ^ 2) ∂ν :=
      integral_mono_ae hleft (hright.const_mul _) hpoint
    _ = (b - a) ^ 2 * ∫ p, g p ^ 2 ∂((volume.restrict (Icc a b)).prod ν) := by
      rw [integral_const_mul, integral_prod_symm _ hg.integrable_sq]

end EinsteinFull.Regeneration
