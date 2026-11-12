import EinsteinRelation.Correctors.TimeIntegralLpBound
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Source: `paper/main.tex:722,756`. Short positive-time windows have
small moments when their sectionwise moments are bounded by `C/t`. -/
open MeasureTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors

/-- A time window of length `b-a` costs at most `C (b-a)/a` in `L^p`.
The bound applies to the genuine set integral on the closed interval. -/
theorem eLpNorm_short_time_window_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [SFinite μ] {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    {g : Ω × ℝ → ℝ} (hg : Measurable g)
    {a b C : ℝ} (ha : 0 < a) (hab : a < b) (hC : 0 < C)
    (hbound : ∀ t ∈ Set.Icc a b,
      eLpNorm (fun ω => g (ω, t)) p μ ≤ ENNReal.ofReal (C / t)) :
    eLpNorm (fun ω => ∫ t in Set.Icc a b, g (ω, t)) p μ ≤
      ENNReal.ofReal (C * (b - a) / a) := by
  have hBa : 0 < C / a := div_pos hC ha
  have hI : (∫ _t in Set.Icc a b, C / a) = C * (b - a) / a := by
    simp only [integral_const, smul_eq_mul, measureReal_def,
      Measure.restrict_apply_univ, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le)]
    ring
  have hBi : IntegrableOn (fun _t : ℝ => C / a) (Set.Icc a b) :=
    integrableOn_const (by simpa only [Real.volume_Icc] using
      (ENNReal.ofReal_ne_top : ENNReal.ofReal (b - a) ≠ ∞))
  have h := eLpNorm_setIntegral_le_integral_bound (μ := μ) volume
    measurableSet_Icc hp hpt hg measurable_const hBi (fun _ => hBa)
    (by rw [hI]; exact div_pos (mul_pos hC (sub_pos.mpr hab)) ha)
    (fun t ht => (hbound t ht).trans (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_left hC.le ha ht.1)))
  rwa [hI] at h

end EinsteinRelation.Correctors
