import EinsteinRelation.External.AKMLocalCorrectors
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors
open External.AKM

/-- Exact conversion between local Euclidean L² energy and RMS, including
a zero-measure domain. Source: `paper/main.tex:798–806`. -/
theorem eLpNorm_euclideanNorm_toReal_eq_volume_mul_rms {X : Type*}
    [MeasurableSpace X] {d : ℕ} (μ : Measure X) (U : Set X)
    [IsFiniteMeasure (μ.restrict U)] (G : X → Vec d)
    (hG : MemLp (fun x => euclideanNorm (G x)) 2 (μ.restrict U)) :
    (eLpNorm (fun x => euclideanNorm (G x)) 2 (μ.restrict U)).toReal =
      Real.sqrt ((μ U).toReal) * vectorRms μ U G := by
  have hs (x : X) : 0 ≤ euclideanSq (G x) := by
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg (G x i)
  have hn : (eLpNorm (fun x => euclideanNorm (G x)) 2 (μ.restrict U)).toReal =
      Real.sqrt (∫ x in U, euclideanSq (G x) ∂μ) := by
    rw [hG.eLpNorm_eq_integral_rpow_norm (by norm_num : (2 : ENNReal) ≠ 0)
      (by norm_num : (2 : ENNReal) ≠ ⊤), ENNReal.toReal_ofReal (by positivity),
      Real.sqrt_eq_rpow]
    congr 1
    · apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs,
          euclideanNorm, Real.sq_sqrt (hs x)]
    · norm_num
  rw [hn]
  simp only [vectorRms, average_eq, Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
  by_cases hV : (μ U).toReal = 0
  · have hfin : μ U ≠ ⊤ := by
      simpa only [Measure.restrict_apply_univ] using
        measure_ne_top (μ.restrict U) Set.univ
    have hz : μ U = 0 := ((ENNReal.toReal_eq_zero_iff (μ U)).mp hV).resolve_right hfin
    simp [hz]
  · rw [← Real.sqrt_mul ENNReal.toReal_nonneg, ← mul_assoc, mul_inv_cancel₀ hV, one_mul]

end EinsteinRelation.Correctors
