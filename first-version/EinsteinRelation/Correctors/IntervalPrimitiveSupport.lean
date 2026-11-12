import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus


open MeasureTheory Filter Topology
namespace EinsteinRelation.Correctors

theorem intervalPrimitive_eq_zero_of_le_left {a t : ℝ} {η : ℝ → ℝ}
    (hη : Continuous η) (hs : ∀ x, x ≤ a → η x = 0) (ht : t ≤ a) :
    (∫ s in a..t, η s) = 0 := by
  have h0 : (∫ s in a..t, η s) = ∫ s in a..t, (0 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_ge ht] at hx
    exact hs x hx.2
  rw [h0]
  simp

theorem intervalPrimitive_eq_zero_of_ge_right {a b t : ℝ} {η : ℝ → ℝ}
    (hab : a ≤ b) (hη : Continuous η) (hc : HasCompactSupport η)
    (hs : Function.support η ⊆ Set.Icc a b)
    (hz : (∫ s : ℝ, η s) = 0) (ht : b ≤ t) :
    (∫ s in a..t, η s) = 0 := by
  -- η agrees with its restriction to Icc a b, since its support lies there
  have hfun : Set.indicator (Set.Icc a b) η = η := by
    funext x
    by_cases hx : x ∈ Set.Icc a b
    · exact Set.indicator_of_mem hx η
    · rw [Set.indicator_of_notMem hx]
      by_contra h
      exact hx (hs (Function.mem_support.mpr (Ne.symm h)))
  have hzIcc : ∫ s in Set.Icc a b, η s = 0 := by
    have hind : (∫ s, Set.indicator (Set.Icc a b) η s) = ∫ s in Set.Icc a b, η s :=
      integral_indicator measurableSet_Icc
    rw [hfun, hz] at hind
    exact hind.symm
  have hab_int : ∫ s in a..b, η s = 0 := by
    rw [intervalIntegral.integral_of_le hab, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    exact hzIcc
  have hbt : ∫ s in b..t, η s = 0 := by
    have h0 : (∫ s in b..t, η s) = ∫ s in b..t, (0 : ℝ) := by
      apply intervalIntegral.integral_congr_ae
      refine Filter.Eventually.of_forall (fun x hx => ?_)
      rw [Set.uIoc_of_le ht] at hx
      by_contra h
      have hxI : x ∈ Set.Icc a b := hs (Function.mem_support.mpr h)
      exact absurd hxI.2 (not_le.mpr hx.1)
    rw [h0]
    simp
  rw [← intervalIntegral.integral_add_adjacent_intervals (hη.intervalIntegrable a b)
    (hη.intervalIntegrable b t), hab_int, hbt, add_zero]

end EinsteinRelation.Correctors
