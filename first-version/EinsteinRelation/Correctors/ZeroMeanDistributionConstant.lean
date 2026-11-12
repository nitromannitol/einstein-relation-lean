import EinsteinRelation.Correctors.ContinuousDistributionalConstant
import EinsteinRelation.Correctors.ZeroMeanTestNormalization
import EinsteinRelation.Correctors.SmoothUnitIntervalTest
import EinsteinRelation.Correctors.UnitMeanPairingAlgebra

/-! Distributional constantness for continuous scalar functions; source `paper/main.tex:808–816`. -/
open MeasureTheory
namespace EinsteinRelation.Correctors

theorem integrable_mul_of_continuousOn_tsupport_subset {a b : ℝ}
    (U : ℝ → ℝ) (hU : ContinuousOn U (Set.Icc a b)) (η : ℝ → ℝ)
    (hη : Continuous η) (hs : tsupport η ⊆ Set.Ioo a b) :
    MeasureTheory.Integrable (fun t => U t * η t) := by
  -- `U * η` vanishes off `Icc a b`, so it is the indicator of its restriction.
  have hind : (fun t => U t * η t) =
      Set.indicator (Set.Icc a b) (fun t => U t * η t) := by
    funext t
    by_cases ht : t ∈ Set.Icc a b
    · rw [Set.indicator_of_mem ht]
    · have hnt : t ∉ tsupport η := fun h => ht (Set.Ioo_subset_Icc_self (hs h))
      rw [image_eq_zero_of_notMem_tsupport hnt, Set.indicator_of_notMem ht]
      simp
  rw [hind]
  exact ((hU.mul hη.continuousOn).integrableOn_Icc).integrable_indicator measurableSet_Icc

theorem exists_constant_of_zero_mean_smooth_pairings {a b : ℝ} (hab : a < b)
    (U : ℝ → ℝ) (hU : ContinuousOn U (Set.Icc a b))
    (hzero : ∀ η : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      tsupport η ⊆ Set.Ioo a b → (∫ t : ℝ, η t) = 0 →
      (∫ t : ℝ, U t * η t) = 0) :
    ∃ c : ℝ, Set.EqOn U (fun _ => c) (Set.Icc a b) := by
  obtain ⟨ρ, hρc, hρcs, hρs, hρ1⟩ := exists_smooth_unit_integral_test_Ioo hab
  refine ⟨∫ t : ℝ, U t * ρ t, eqOn_const_of_smooth_test_pairings hab U hU ?_⟩
  intro η hηc hηcs hηs
  obtain ⟨h1, h2, h3, h4⟩ := smooth_test_sub_unit_mean ρ η hρc hηc hρcs hηcs hρs hηs hρ1
  have hz := hzero (fun t => η t - (∫ s : ℝ, η s) * ρ t) h1 h2 h3 h4
  have hUη := integrable_mul_of_continuousOn_tsupport_subset U hU η hηc.continuous hηs
  have hUρ := integrable_mul_of_continuousOn_tsupport_subset U hU ρ hρc.continuous hρs
  have hpair := integral_pairing_of_unit_mean_subtraction U ρ η hUη hUρ hz
  have hη_int : MeasureTheory.Integrable η :=
    hηc.continuous.integrable_of_hasCompactSupport hηcs
  calc ∫ t : ℝ, η t * (U t - ∫ s : ℝ, U s * ρ s)
      = ∫ t : ℝ, (U t * η t - (∫ s : ℝ, U s * ρ s) * η t) := by
        congr 1
        funext t
        ring
    _ = (∫ t : ℝ, U t * η t) - (∫ s : ℝ, U s * ρ s) * (∫ t : ℝ, η t) := by
        rw [integral_sub hUη (hη_int.const_mul _), integral_const_mul]
    _ = 0 := by
        rw [hpair]
        ring

end EinsteinRelation.Correctors
