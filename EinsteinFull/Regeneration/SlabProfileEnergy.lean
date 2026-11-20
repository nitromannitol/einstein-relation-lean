import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-!
# Exponential boundary profile bounds

The width-one boundary layer and transverse box in Gantert–Mathieu–Piatnitski,
Lemma 4.4, have an exponentially small weighted volume.
-/

open MeasureTheory Set
open scoped ENNReal

namespace EinsteinFull.Regeneration

/-- The exponential weight on the unit boundary layer has exponentially small mass. -/
theorem integral_exp_boundary_layer_le (s L : ℝ) (hs : 0 ≤ s) :
    (∫ t in Ioc (-L) (-L + 1), Real.exp (s * t)) ≤
      Real.exp s * Real.exp (-(s * L)) := by
  have hint : IntegrableOn (fun t : ℝ => Real.exp (s * t)) (Ioc (-L) (-L + 1)) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).integrableOn_Ioc
  have hconst : IntegrableOn (fun _ : ℝ => Real.exp (s * (-L + 1)))
      (Ioc (-L) (-L + 1)) := by
    let : IsFiniteMeasure (volume.restrict (Ioc (-L) (-L + 1)) : Measure ℝ) := by
      infer_instance
    exact integrable_const _
  have hbound := setIntegral_mono_on hint hconst measurableSet_Ioc (fun t ht =>
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hs))
  have hnorm : (∫ _t in Ioc (-L) (-L + 1), Real.exp (s * (-L + 1))) =
      Real.exp (s * (-L + 1)) := by
    simp
  rw [hnorm] at hbound
  calc
    _ ≤ Real.exp (s * (-L + 1)) := hbound
    _ = Real.exp s * Real.exp (-(s * L)) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- The transverse volume factor leaves exactly one inverse-dimensional decay. -/
theorem boundary_layer_transverse_factor (n : ℕ) (s L : ℝ) :
    (2 * Real.exp (s * L / (n + 1))) ^ n * Real.exp (-(s * L)) =
      2 ^ n * Real.exp (-(s * L / (n + 1))) := by
  rw [mul_pow, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
  congr 2
  have hn : (0 : ℝ) < n + 1 := by positivity
  field_simp
  ring

/-- The Euclidean volume of a transverse coordinate cube. -/
theorem volume_transverse_cube (n : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    (volume : Measure (Fin n → ℝ)).real (Icc (fun _ => -R) (fun _ => R)) = (2 * R) ^ n := by
  have hle : (fun _ : Fin n => -R) ≤ (fun _ : Fin n => R) := fun _ => by linarith
  have h := Real.volume_Icc_pi_toReal hle
  simpa only [measureReal_def, Pi.sub_apply, sub_neg_eq_add, ← two_mul,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h

/-- The weighted boundary layer has the decay rate used in the source competitor. -/
theorem weighted_boundary_layer_volume_le (n : ℕ) (s L : ℝ) (hs : 0 ≤ s) :
    (∫ t in Ioc (-L) (-L + 1), Real.exp (s * t)) *
      (volume : Measure (Fin n → ℝ)).real
        (Icc (fun _ => -Real.exp (s * L / (n + 1)))
          (fun _ => Real.exp (s * L / (n + 1)))) ≤
      Real.exp s * 2 ^ n * Real.exp (-(s * L / (n + 1))) := by
  rw [volume_transverse_cube n _ (Real.exp_pos _).le]
  calc
    _ ≤ (Real.exp s * Real.exp (-(s * L))) *
        (2 * Real.exp (s * L / (n + 1))) ^ n :=
      mul_le_mul_of_nonneg_right (integral_exp_boundary_layer_le s L hs) (by positivity)
    _ = Real.exp s * ((2 * Real.exp (s * L / (n + 1))) ^ n *
        Real.exp (-(s * L))) := by ring
    _ = _ := by rw [boundary_layer_transverse_factor]; ring

end EinsteinFull.Regeneration
