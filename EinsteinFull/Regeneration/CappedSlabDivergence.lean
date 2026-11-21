import EinsteinFull.Regeneration.CappedSlabIncrements
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Divergence of the capped slab clock

A capped step either lasts the whole cap or traverses the slab radius.
Continuity prevents infinitely many such steps in a bounded time interval.
-/

open Filter EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal Topology

namespace EinsteinFull.Regeneration

/-- A capped slab step either reaches the cap or exits at the slab boundary. -/
theorem capped_step_time_or_displacement {d : ℕ} (γ : Path d) (i : Fin d)
    (r : ℝ) (hr : 0 < r) (g : ℝ≥0) (n : ℕ) :
    g ≤ cappedCoordinateSlabExit (pathTimeShift γ (cappedSlabExitTime γ i r g n)) i r g ∨
      r ≤ |γ (cappedSlabExitTime γ i r g (n + 1)) i -
        γ (cappedSlabExitTime γ i r g n) i| := by
  let η := pathTimeShift γ (cappedSlabExitTime γ i r g n)
  by_cases hfin : coordinateSlabExit η i r = ⊤
  · left
    simp [cappedCoordinateSlabExit, η, hfin]
  · rcases le_total (coordinateSlabExit η i r).toNNReal g with hle | hle
    · right
      have heq : cappedCoordinateSlabExit η i r g = (coordinateSlabExit η i r).toNNReal := by
        simp [cappedCoordinateSlabExit, hfin, min_eq_left hle]
      have h := coordinate_slab_exit_displacement η i r hr hfin
      change |η (coordinateSlabExit η i r).toNNReal i - η 0 i| = r at h
      rw [← heq] at h
      rw [cappedSlabExitTime_succ]
      simpa only [η, pathTimeShift, ContinuousMap.coe_mk, add_zero] using h.ge
    · left
      simp [cappedCoordinateSlabExit, η, hfin, min_eq_right hle]

/-- The positive capped slab clock cannot accumulate in finite time. -/
theorem capped_slab_exit_times_tendsto_atTop {d : ℕ} (γ : Path d) (i : Fin d)
    (r : ℝ) (hr : 0 < r) (g : ℝ≥0) (hg : 0 < g) :
    Tendsto (cappedSlabExitTime γ i r g) atTop atTop := by
  let τ := cappedSlabExitTime γ i r g
  have hmono : Monotone τ := monotone_cappedSlabExitTime γ i r g
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
  let T : ℝ≥0 := ⨆ n, τ n
  have ht : Tendsto τ atTop (𝓝 T) := tendsto_atTop_ciSup hmono hbdd
  have ht' : Tendsto (fun n : ℕ => (τ n : ℝ)) atTop (𝓝 (T : ℝ)) :=
    NNReal.continuous_coe.continuousAt.tendsto.comp ht
  have htNext := ht'.comp (tendsto_add_atTop_nat 1)
  have htime : Tendsto (fun n : ℕ => (τ (n + 1) : ℝ) - τ n) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, sub_self] using htNext.sub ht'
  have hc : Continuous (fun t : ℝ≥0 => γ t i) := (continuous_apply i).comp γ.continuous
  have hx : Tendsto (fun n : ℕ => γ (τ n) i) atTop (𝓝 (γ T i)) :=
    (hc.tendsto _).comp ht
  have hxNext := hx.comp (tendsto_add_atTop_nat 1)
  have hspace : Tendsto (fun n : ℕ => |γ (τ (n + 1)) i - γ (τ n) i|) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, sub_self, abs_zero] using (hxNext.sub hx).abs
  have hbound (n : ℕ) : min (g : ℝ) r ≤
      ((τ (n + 1) : ℝ) - τ n) + |γ (τ (n + 1)) i - γ (τ n) i| := by
    have htime0 : 0 ≤ (τ (n + 1) : ℝ) - τ n := by
      exact sub_nonneg.mpr (NNReal.coe_le_coe.mpr (hmono (Nat.le_succ n)))
    have hspace0 : 0 ≤ |γ (τ (n + 1)) i - γ (τ n) i| := abs_nonneg _
    rcases capped_step_time_or_displacement γ i r hr g n with hcap | hdisp
    · have hcap' : (g : ℝ) ≤ (τ (n + 1) : ℝ) - τ n := by
        have he : (g : ℝ) ≤
            (cappedCoordinateSlabExit (pathTimeShift γ (τ n)) i r g : ℝ) :=
          NNReal.coe_le_coe.mpr hcap
        simp only [τ, cappedSlabExitTime_succ, NNReal.coe_add] at he ⊢
        linarith
      exact (min_le_left _ _).trans (by linarith)
    · exact (min_le_right _ _).trans (by linarith)
  have h := ge_of_tendsto' (by simpa only [zero_add] using htime.add hspace) hbound
  have hg' : (0 : ℝ) < g := NNReal.coe_pos.mpr hg
  exact (not_le_of_gt (lt_min hg' hr)) h

end EinsteinFull.Regeneration
