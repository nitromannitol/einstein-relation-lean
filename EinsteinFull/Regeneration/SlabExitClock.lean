import EinsteinFull.Regeneration.SlabWalkDomination
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Divergence of slab exit times

Successive exits separated by a fixed positive spatial distance cannot
accumulate in finite time along a continuous path.
-/

open Filter EinsteinRelation
open scoped NNReal Topology

namespace EinsteinFull.Regeneration

/-- Monotone times with uniformly separated coordinate positions tend to infinity. -/
theorem slab_exit_times_tendsto_atTop {d : ℕ} (γ : Path d) (i : Fin d)
    (τ : ℕ → ℝ≥0) (hmono : Monotone τ) (r : ℝ) (hr : 0 < r)
    (hsep : ∀ n, r ≤ |γ (τ (n + 1)) i - γ (τ n) i|) :
    Tendsto τ atTop atTop := by
  by_contra hnot
  have hbdd : BddAbove (Set.range τ) := by
    by_contra h
    apply hnot
    apply tendsto_atTop_atTop_of_monotone hmono
    intro b
    by_contra hn
    push Not at hn
    apply h
    refine ⟨b, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (hn n).le
  have ht : Tendsto τ atTop (𝓝 (⨆ n, τ n)) := tendsto_atTop_ciSup hmono hbdd
  have hc : Continuous (fun t : ℝ≥0 => γ t i) := (continuous_apply i).comp γ.continuous
  have hx : Tendsto (fun n : ℕ => γ (τ n) i) atTop (𝓝 (γ (⨆ n, τ n) i)) :=
    (hc.tendsto _).comp ht
  have hx' : Tendsto (fun n : ℕ => γ (τ (n + 1)) i) atTop (𝓝 (γ (⨆ n, τ n) i)) :=
    hx.comp (tendsto_add_atTop_nat 1)
  have hdiff : Tendsto (fun n : ℕ => |γ (τ (n + 1)) i - γ (τ n) i|) atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero] using (hx'.sub hx).abs
  have hr0 : r ≤ 0 := ge_of_tendsto' hdiff hsep
  exact (not_le_of_gt hr) hr0

end EinsteinFull.Regeneration
