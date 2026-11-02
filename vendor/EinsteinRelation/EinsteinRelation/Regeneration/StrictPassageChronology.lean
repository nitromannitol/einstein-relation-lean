import EinsteinRelation.Diffusion.Basic
import EinsteinRelation.Probability.HittingTimes
import Mathlib.Topology.Order.Compact

open EinsteinRelation MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinRelation.Regeneration

/-!
Strict passage chronology for the upward hitting times `T_u` of the coordinate `e_1`
(`paper/main.tex:280–287`). For `R > 0`, the next hitting time `T_{M(t)+R}` is strictly later
than `t`, where `M(t)` is the running maximum of the coordinate on `[0, t]`.

The infimum is taken in `ℝ≥0∞` with value `⊤` on the empty set. The eligible times form a
closed set, so an infimum at most `t` is attained at some time `u ≤ t`. The compact supremum
bounds the displacement at `u` by `M(t)`, which contradicts `M(t) + R ≤ displacement` when
`R > 0`. No chronology assumption is used.
-/

/-- A closed set of times whose infimum (in `ℝ≥0∞`, with value `⊤` on the empty set) is at
most `T` contains a time at most `T`: the infimum is attained because the set is closed. -/
private theorem exists_le_of_iInf_le_coe {S : Set ℝ≥0} (hS : IsClosed S) {T : ℝ≥0}
    (h : (⨅ (u : ℝ≥0) (_ : u ∈ S), (u : ℝ≥0∞)) ≤ (T : ℝ≥0∞)) :
    ∃ u ∈ S, u ≤ T := by
  by_cases hne : S.Nonempty
  · have hcoe : (↑(sInf S) : ℝ≥0∞) = ⨅ (u : ℝ≥0) (_ : u ∈ S), (u : ℝ≥0∞) :=
      ENNReal.coe_sInf hne
    rw [← hcoe, ENNReal.coe_le_coe] at h
    exact ⟨sInf S, hS.csInf_mem hne (OrderBot.bddBelow S), h⟩
  · have htop : (⨅ (u : ℝ≥0) (_ : u ∈ S), (u : ℝ≥0∞)) = ⊤ := by
      apply le_antisymm le_top
      refine le_iInf fun u => le_iInf fun hu => ?_
      exact (hne ⟨u, hu⟩).elim
    rw [htop] at h
    exact (ENNReal.coe_ne_top (top_le_iff.mp h)).elim

/-- For `R > 0`, the upward hitting time at level `M(t) + R` is strictly later than `t`
(`paper/main.tex:280–287`). The compact supremum bounds the displacement on `[0, t]` by
`M(t)`, so no eligible time `u ≤ t` exists. -/
theorem lt_upcrossing_above_coordinate_maximum {d : ℕ} (γ : Path d)
    (i : Fin d) (t : ℝ≥0) (R : ℝ) (hR : 0 < R) :
    (t : ℝ≥0∞) <
      ⨅ (u : ℝ≥0) (_ :
        sSup ((fun v : ℝ≥0 => γ v i - γ 0 i) '' Set.Icc (0 : ℝ≥0) t) + R ≤
          γ u i - γ 0 i), (u : ℝ≥0∞) := by
  have hc : Continuous (fun v : ℝ≥0 => γ v i - γ 0 i) :=
    ((continuous_apply i).comp γ.continuous).sub continuous_const
  have hK : IsCompact (Set.Icc (0 : ℝ≥0) t) := isCompact_Icc
  have hbdd : BddAbove ((fun v : ℝ≥0 => γ v i - γ 0 i) '' Set.Icc (0 : ℝ≥0) t) :=
    IsCompact.bddAbove_image hK hc.continuousOn
  have hclosed : IsClosed {u : ℝ≥0 |
      sSup ((fun v : ℝ≥0 => γ v i - γ 0 i) '' Set.Icc (0 : ℝ≥0) t) + R ≤ γ u i - γ 0 i} :=
    isClosed_le continuous_const hc
  by_contra hcon
  obtain ⟨u, hu, hut⟩ := exists_le_of_iInf_le_coe hclosed (not_lt.mp hcon)
  have hu' : sSup ((fun v : ℝ≥0 => γ v i - γ 0 i) '' Set.Icc (0 : ℝ≥0) t) + R ≤
      γ u i - γ 0 i := hu
  have hmem : (fun v : ℝ≥0 => γ v i - γ 0 i) u ∈
      (fun v : ℝ≥0 => γ v i - γ 0 i) '' Set.Icc (0 : ℝ≥0) t :=
    ⟨u, Set.mem_Icc.mpr ⟨zero_le, hut⟩, rfl⟩
  have hdisp : γ u i - γ 0 i ≤
      sSup ((fun v : ℝ≥0 => γ v i - γ 0 i) '' Set.Icc (0 : ℝ≥0) t) :=
    le_csSup hbdd hmem
  linarith only [hu', hdisp, hR]

end EinsteinRelation.Regeneration
