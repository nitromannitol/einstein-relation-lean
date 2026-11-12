import EinsteinRelation.Correctors.EuclideanTimeSpaceCauchy
import Mathlib.MeasureTheory.Integral.Average

open MeasureTheory Set
namespace EinsteinRelation.Correctors

/-- Spatial normalization of the literal integrated gradient retains the
ratio of the outer and inner volumes. Source: `paper/main.tex:852–857`. -/
theorem integrated_gradient_setAverage_le_energy_envelope
    {d : ℕ} {T : ℝ} (hT : 0 ≤ T) {U V : Set (Vec d)}
    (hU : 0 < volume.real U) (hV : 0 < volume.real V)
    (G : ℝ × Vec d → Vec d) (e : ℝ → Vec d → ℝ)
    (hG : MemLp G 2 ((volume.restrict (Icc 0 T)).prod (volume.restrict V)))
    (henergy : (∫ t in Icc (0 : ℝ) T, ∫ x in V, euclideanSq (G (t,x))) ≤
      ∫ t in Icc (0 : ℝ) T, ∫ x in U, e t x) :
    Real.sqrt (⨍ x in V, euclideanSq (∫ t in Icc (0 : ℝ) T, G (t,x))) ≤
      Real.sqrt (volume.real U / volume.real V) *
        Real.sqrt (T * ∫ t in Icc (0 : ℝ) T, ⨍ x in U, e t x) := by
  have hcs := integral_euclideanSq_time_integral_le (volume.restrict V) hT hG
  have hle :
      (volume.real V)⁻¹ * (∫ x in V, euclideanSq (∫ t in Icc (0 : ℝ) T, G (t,x))) ≤
        (volume.real U / volume.real V) *
          (T * ∫ t in Icc (0 : ℝ) T, ⨍ x in U, e t x) := by
    simp only [setAverage_eq, smul_eq_mul, integral_const_mul]
    have hv := mul_le_mul_of_nonneg_left
      (hcs.trans (mul_le_mul_of_nonneg_left henergy hT)) (inv_nonneg.mpr hV.le)
    convert hv using 1
    field_simp [hU.ne', hV.ne']
  rw [setAverage_eq, smul_eq_mul]
  calc
    _ ≤ Real.sqrt ((volume.real U / volume.real V) *
        (T * ∫ t in Icc (0 : ℝ) T, ⨍ x in U, e t x)) := Real.sqrt_le_sqrt hle
    _ = _ := Real.sqrt_mul (div_nonneg hU.le hV.le) _

end EinsteinRelation.Correctors
