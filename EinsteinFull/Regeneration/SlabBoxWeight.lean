import EinsteinFull.Regeneration.SlabProfileEnergy
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Exponential weight on a slab box

Integrating the force weight over the full box gives the initial energy
scale used in the slab comparison.
-/

open MeasureTheory Set
open scoped ENNReal

namespace EinsteinFull.Regeneration

/-- The exponential mass below the positive face bounds its mass on the slab. -/
theorem integral_exp_slab_le (s L : ℝ) (hs : 0 < s) :
    (∫ t in Icc (-L) L, Real.exp (s * t)) ≤ Real.exp (s * L) / s := by
  have hint : IntegrableOn (fun t : ℝ => Real.exp (s * t)) (Iic L) :=
    integrableOn_exp_mul_Iic hs L
  have hnonneg : ∀ᵐ t ∂(volume.restrict (Iic L)), 0 ≤ Real.exp (s * t) :=
    Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le
  have h := setIntegral_mono_set hint hnonneg
    (Filter.Eventually.of_forall (show Icc (-L) L ⊆ Iic L from fun _ ht => ht.2))
  rw [integral_exp_mul_Iic hs L] at h
  exact h

/-- The force and transverse factors give the full-box exponential rate. -/
theorem weighted_slab_product_volume_le (n : ℕ) (s L : ℝ) (hs : 0 < s) :
    (∫ t in Icc (-L) L, Real.exp (s * t)) *
      (volume : Measure (Fin n → ℝ)).real
        (Icc (fun _ => -Real.exp (s * L / (n + 1)))
          (fun _ => Real.exp (s * L / (n + 1)))) ≤
      ((2 : ℝ) ^ n / s) * Real.exp ((s * (2 * (n + 1 : ℝ) - 1) / (n + 1)) * L) := by
  rw [volume_transverse_cube n _ (Real.exp_pos _).le]
  have h := mul_le_mul_of_nonneg_right (integral_exp_slab_le s L hs)
    (show 0 ≤ (2 * Real.exp (s * L / (n + 1))) ^ n by positivity)
  apply h.trans_eq
  rw [mul_pow, ← Real.exp_nat_mul]
  have he : s * L + (n : ℝ) * (s * L / (n + 1)) =
      (s * (2 * (n + 1 : ℝ) - 1) / (n + 1)) * L := by
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  calc
    _ = ((2 : ℝ) ^ n / s) * (Real.exp (s * L) *
        Real.exp ((n : ℝ) * (s * L / (n + 1)))) := by ring
    _ = _ := by rw [← Real.exp_add, he]

end EinsteinFull.Regeneration
