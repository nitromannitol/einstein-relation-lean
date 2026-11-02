import EinsteinRelation.Probability.DowncrossingEvents
import Mathlib.Topology.Order.Monotone
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-! # Literal continuous-path downward hitting times

Source: `paper/main.tex:301–306` (`regen.D`). The extended infimum includes
threshold touches; its finite-horizon sublevel is exactly the actual compact-time
crossing event. No new source-facing hitting-time definition is introduced.
-/

open scoped NNReal ENNReal

namespace EinsteinRelation.Probability

theorem downcrossing_inf_le_iff {d : ℕ} (γ : Path d) (i : Fin d) (a : ℝ) (T : ℝ≥0) :
    (⨅ (t : ℝ≥0) (_ : γ t i - γ 0 i ≤ a), (t : ℝ≥0∞)) ≤ (T : ℝ≥0∞) ↔
      ∃ t ∈ Set.Icc (0 : ℝ≥0) T, γ t i - γ 0 i ≤ a := by
  let S : Set ℝ≥0 := {t | γ t i - γ 0 i ≤ a}
  by_cases hS : S.Nonempty
  · have hclosed : IsClosed S :=
      isClosed_le (((continuous_apply i).comp γ.continuous).sub continuous_const)
        continuous_const
    have hcoe : ((sInf S : ℝ≥0) : ℝ≥0∞) =
        ⨅ (t : ℝ≥0) (_ : γ t i - γ 0 i ≤ a), (t : ℝ≥0∞) :=
      ENNReal.coe_sInf hS
    rw [← hcoe, ENNReal.coe_le_coe]
    constructor
    · intro h
      exact ⟨sInf S, ⟨zero_le, h⟩, hclosed.csInf_mem hS (OrderBot.bddBelow S)⟩
    · rintro ⟨t, ht, ha⟩
      exact (csInf_le (OrderBot.bddBelow S) ha).trans ht.2
  · have htop : (⨅ (t : ℝ≥0) (_ : γ t i - γ 0 i ≤ a), (t : ℝ≥0∞)) = ⊤ := by
      apply le_antisymm le_top
      refine le_iInf fun t => le_iInf fun ht => ?_
      exact (hS ⟨t, ht⟩).elim
    constructor
    · intro h
      rw [htop] at h
      exact (ENNReal.coe_ne_top (top_le_iff.mp h)).elim
    · rintro ⟨t, _, ht⟩
      exact (hS ⟨t, ht⟩).elim

/-- Literal downward hitting time is measurable on actual continuous paths. -/
theorem measurable_downcrossing_inf {d : ℕ} (i : Fin d) (a : ℝ) :
    Measurable (fun γ : Path d =>
      ⨅ (t : ℝ≥0) (_ : γ t i - γ 0 i ≤ a), (t : ℝ≥0∞)) := by
  apply measurable_of_Iic
  intro T
  by_cases hT : T = ⊤
  · subst T
    simp
  · rw [← ENNReal.coe_toNNReal hT]
    have hset : (fun γ : Path d =>
        ⨅ (t : ℝ≥0) (_ : γ t i - γ 0 i ≤ a), (t : ℝ≥0∞)) ⁻¹'
        Set.Iic (T.toNNReal : ℝ≥0∞) =
        {γ : Path d | ∃ t ∈ Set.Icc (0 : ℝ≥0) T.toNNReal, γ t i - γ 0 i ≤ a} := by
      ext γ
      exact downcrossing_inf_le_iff γ i a T.toNNReal
    rw [hset]
    simpa only [neg_neg] using
      (isClosed_downcrossing_by i (-a) T.toNNReal).measurableSet

/-- Infinity means there is no threshold touch at any finite time. -/
theorem downcrossing_inf_eq_top_iff {d : ℕ} (γ : Path d) (i : Fin d) (a : ℝ) :
    (⨅ (t : ℝ≥0) (_ : γ t i - γ 0 i ≤ a), (t : ℝ≥0∞)) = ⊤ ↔
      ∀ t : ℝ≥0, a < γ t i - γ 0 i := by
  constructor
  · intro h t
    by_contra ht
    have hbound : (⨅ (u : ℝ≥0) (_ : γ u i - γ 0 i ≤ a), (u : ℝ≥0∞)) ≤
        (t : ℝ≥0∞) := iInf_le_of_le t (iInf_le_of_le (not_lt.mp ht) le_rfl)
    rw [h] at hbound
    exact ENNReal.coe_ne_top (top_le_iff.mp hbound)
  · intro h
    apply le_antisymm le_top
    refine le_iInf fun t => le_iInf fun ht => ?_
    exact (not_le_of_gt (h t) ht).elim

end EinsteinRelation.Probability
