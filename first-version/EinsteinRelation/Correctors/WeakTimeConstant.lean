import EinsteinRelation.Correctors.ZeroMeanDistributionConstant
import EinsteinRelation.Correctors.ZeroMeanTestPrimitive

/-! Endpoint traces from the actual weak time equation;
source `paper/main.tex:808–816,833–848`. -/
open MeasureTheory
namespace EinsteinRelation.Correctors

theorem endpoints_eq_of_integral_mul_deriv_eq_zero {a b : ℝ} (hab : a < b)
    (U : ℝ → ℝ) (hU : ContinuousOn U (Set.Icc a b))
    (hweak : ∀ η : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      tsupport η ⊆ Set.Ioo a b → (∫ t in a..b, U t * deriv η t) = 0) :
    U b = U a := by
  obtain ⟨c, hc⟩ := exists_constant_of_zero_mean_smooth_pairings hab U hU (by
    intro η hη hηc hηs hηzero
    obtain ⟨ζ, hζ, hζc, hζs, hdζ⟩ :=
      exists_compact_primitive_of_integral_eq_zero hab hη hηc hηs hηzero
    have hz := hweak ζ hζ hζc hζs
    simp_rw [hdζ] at hz
    rw [intervalIntegral.integral_of_le hab.le] at hz
    have hind : (Set.Ioc a b).indicator (fun t => U t * η t) =
        (fun t => U t * η t) := by
      funext t
      by_cases ht : t ∈ Set.Ioc a b
      · exact Set.indicator_of_mem ht _
      · rw [Set.indicator_of_notMem ht]
        have hnt : t ∉ tsupport η := fun h => ht ⟨(hηs h).1, (hηs h).2.le⟩
        rw [image_eq_zero_of_notMem_tsupport hnt, mul_zero]
    rw [← hind, integral_indicator measurableSet_Ioc]
    exact hz)
  exact (hc (Set.right_mem_Icc.mpr hab.le)).trans
    (hc (Set.left_mem_Icc.mpr hab.le)).symm

end EinsteinRelation.Correctors
