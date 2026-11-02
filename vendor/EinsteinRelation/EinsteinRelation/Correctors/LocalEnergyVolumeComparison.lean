import EinsteinRelation.External.AKMLocalCorrectors
import Mathlib.MeasureTheory.Function.L2Space

/-! # Volume comparison for local Euclidean energy

Source: `paper/main.tex:788–796,850–858`. Restricting an energy integral
costs the square root of the volume ratio for normalized RMS norms.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors
open External.AKM

/-- Passing to a smaller averaging set retains its exact normalization.
Source: `paper/main.tex:788–796,850–858`. -/
theorem vectorRms_mono_set_volume_ratio {d : ℕ} {X : Type*} [MeasurableSpace X]
    (ν : Measure X) {V U : Set X} (hVU : V ⊆ U)
    (hV : ν V ≠ 0) (hVfin : ν V ≠ ⊤) (hUfin : ν U ≠ ⊤)
    (G : X → Vec d) (hG : MemLp (fun x => euclideanNorm (G x)) 2 (ν.restrict U)) :
    vectorRms ν V G ≤ Real.sqrt ((ν U).toReal / (ν V).toReal) * vectorRms ν U G := by
  have hUv : ν U ≠ 0 := ne_zero_of_lt (lt_of_lt_of_le (pos_iff_ne_zero.mpr hV) (measure_mono hVU))
  have hVr : 0 < (ν V).toReal := ENNReal.toReal_pos hV hVfin
  have hUr : 0 < (ν U).toReal := ENNReal.toReal_pos hUv hUfin
  have hsq (x : X) : 0 ≤ euclideanSq (G x) := by
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun j _ => mul_self_nonneg (G x j)
  have hi : Integrable (fun x => euclideanSq (G x)) (ν.restrict U) := by
    simpa only [euclideanNorm, Real.sq_sqrt (hsq _)] using hG.integrable_sq
  have hle : (∫ x in V, euclideanSq (G x) ∂ν) ≤ ∫ x in U, euclideanSq (G x) ∂ν :=
    setIntegral_mono_set hi (ae_of_all _ hsq) hVU.eventuallyLE
  have hnorm : ((ν U).toReal / (ν V).toReal) *
      ((ν U).toReal)⁻¹ = ((ν V).toReal)⁻¹ := by
    field_simp
  simp only [vectorRms, average_eq, smul_eq_mul, Measure.real, Measure.restrict_apply_univ]
  rw [← Real.sqrt_mul (div_nonneg hUr.le hVr.le), ← mul_assoc, hnorm]
  exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr hVr.le))

end EinsteinRelation.Correctors
