import MarkovProcess.Path.Exhaustion

/-!
# Finite exits and bounded-domain exhaustion

A continuous path with a finite exit time remains in a bounded ball until
that exit. Intersecting the domain with any sufficiently large ball therefore
leaves the path's exit time unchanged.
-/

open Set
open scoped ENNReal NNReal

namespace EinsteinFull.Regeneration

/-- A finite exit is eventually unchanged by intersection with larger balls. -/
theorem exists_ball_exitTime_eq {α : Type*} [PseudoMetricSpace α]
    (U : Set α) (γ : MarkovProcess.ContinuousPath α) (x : α)
    (hfin : MarkovProcess.ContinuousPath.exitTime U γ ≠ ⊤) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      MarkovProcess.ContinuousPath.exitTime (U ∩ Metric.ball x R) γ =
        MarkovProcess.ContinuousPath.exitTime U γ := by
  let τ := MarkovProcess.ContinuousPath.exitTime U γ
  let K := γ '' Icc 0 τ.toNNReal
  have hK : IsCompact K := isCompact_Icc.image γ.continuous
  obtain ⟨r, hr⟩ := hK.isBounded.subset_ball x
  refine ⟨max 1 r, by positivity, ?_⟩
  intro R hR
  apply le_antisymm (MarkovProcess.ContinuousPath.exitTime_mono inter_subset_left γ)
  apply (MarkovProcess.ContinuousPath.le_exitTime_iff (U ∩ Metric.ball x R) γ τ).2
  intro t ht
  apply le_of_not_gt
  intro htτ
  have htu : γ t ∈ U := MarkovProcess.ContinuousPath.mem_of_lt_exitTime U γ t htτ
  have htτ' : t ≤ τ.toNNReal := by
    have hcoe : (t : ℝ≥0∞) ≤ (τ.toNNReal : ℝ≥0∞) := by
      rw [ENNReal.coe_toNNReal hfin]
      exact htτ.le
    exact_mod_cast hcoe
  have hball : γ t ∈ Metric.ball x R := by
    have hmem : γ t ∈ K := ⟨t, ⟨bot_le, htτ'⟩, rfl⟩
    exact Metric.ball_subset_ball ((le_max_right _ _).trans hR) (hr hmem)
  exact ht ⟨htu, hball⟩

end EinsteinFull.Regeneration
