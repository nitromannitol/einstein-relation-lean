import PDEFoundation.Sobolev.OneDimensional.ContinuousWeakIncrement
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Weighted distance to the right face

Monotonicity of the force weight and the one-dimensional increment estimate
bound the weighted distance from a continuous function to its right endpoint.
-/

open MeasureTheory Set PDE
open scoped ENNReal

namespace EinsteinFull.Regeneration

/-- Right-face increments are controlled by weighted derivative energy. -/
theorem weighted_right_face_sq_le {a b s : ℝ} (hab : a < b) (hs : 0 ≤ s)
    (u g : ℝ → ℝ) (hu : ContinuousOn u (Icc a b))
    (hg : MemLp g 2 (volume.restrict (Icc a b)))
    (hinc : ∀ x ∈ Icc a b, u b - u x = ∫ y in x..b, g y) :
    (∫ x in Icc a b, Real.exp (s * x) * (u b - u x) ^ 2) ≤
      (b - a) ^ 2 * ∫ x in Icc a b, Real.exp (s * x) * g x ^ 2 := by
  let E : ℝ := ∫ x in Icc a b, Real.exp (s * x) * g x ^ 2
  have hgint : IntegrableOn g (Icc a b) := hg.integrable (by norm_num)
  have hg2 : IntegrableOn (fun x => g x ^ 2) (Icc a b) := hg.integrable_sq
  have hw : Continuous (fun x : ℝ => Real.exp (s * x)) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hwg2 : IntegrableOn (fun x => Real.exp (s * x) * g x ^ 2) (Icc a b) := by
    apply hg2.bdd_mul hw.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx.2 hs)
  have hE : 0 ≤ E := integral_nonneg fun x => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have huint : IntegrableOn (fun x => Real.exp (s * x) * (u b - u x) ^ 2) (Icc a b) := by
    exact ((hw.continuousOn).mul
      ((continuousOn_const.sub hu).pow 2)).integrableOn_Icc
  have hpoint (x : ℝ) (hx : x ∈ Icc a b) :
      Real.exp (s * x) * (u b - u x) ^ 2 ≤ (b - a) * E := by
    have hlocal : MemLp g 2 (volume.restrict (Icc x b)) :=
      hg.mono_measure (Measure.restrict_mono (Icc_subset_Icc hx.1 le_rfl) le_rfl)
    have hcs := PDE.sq_abs_intervalPrimitive_sub_le_l2 hgint hx ⟨hab.le, le_rfl⟩ hx.2 hlocal
    rw [PDE.intervalPrimitive_sub_eq_intervalIntegral hgint hx ⟨hab.le, le_rfl⟩,
      ← hinc x hx] at hcs
    have hcs' : (u b - u x) ^ 2 ≤ (b - x) * ∫ y in Icc x b, g y ^ 2 := by
      simpa only [Real.rpow_ofNat, sq_abs] using hcs
    have hweight : Real.exp (s * x) * ∫ y in Icc x b, g y ^ 2 ≤ E := by
      rw [← integral_const_mul]
      calc
        (∫ y in Icc x b, Real.exp (s * x) * g y ^ 2) ≤
            ∫ y in Icc x b, Real.exp (s * y) * g y ^ 2 := by
          apply setIntegral_mono_on ((hg2.mono_set (Icc_subset_Icc hx.1 le_rfl)).const_mul _)
            (hwg2.mono_set (Icc_subset_Icc hx.1 le_rfl)) measurableSet_Icc
          intro y hy
          exact mul_le_mul_of_nonneg_right
            (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hy.1 hs)) (sq_nonneg _)
        _ ≤ E := by
          exact setIntegral_mono_set hwg2
            (Filter.Eventually.of_forall fun y => mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
            (Filter.Eventually.of_forall fun _ hy => (Icc_subset_Icc hx.1 le_rfl) hy)
    calc
      Real.exp (s * x) * (u b - u x) ^ 2 ≤
          Real.exp (s * x) * ((b - x) * ∫ y in Icc x b, g y ^ 2) :=
        mul_le_mul_of_nonneg_left hcs' (Real.exp_pos _).le
      _ = (b - x) * (Real.exp (s * x) * ∫ y in Icc x b, g y ^ 2) := by ring
      _ ≤ (b - x) * E := mul_le_mul_of_nonneg_left hweight (sub_nonneg.mpr hx.2)
      _ ≤ (b - a) * E := mul_le_mul_of_nonneg_right (sub_le_sub_left hx.1 b) hE
  calc
    (∫ x in Icc a b, Real.exp (s * x) * (u b - u x) ^ 2) ≤
        ∫ _x in Icc a b, (b - a) * E := by
      exact setIntegral_mono_on huint (integrableOn_const (by simp [Real.volume_Icc]))
        measurableSet_Icc hpoint
    _ = (b - a) ^ 2 * E := by
      rw [setIntegral_const, measureReal_def, Real.volume_Icc,
        ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le)]
      simp only [smul_eq_mul]
      ring

end EinsteinFull.Regeneration
