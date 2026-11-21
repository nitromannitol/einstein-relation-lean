import EinsteinFull.Regeneration.WindowDisplacement
import EinsteinFull.Regeneration.LaterMaximumMeasurability

/-!
# Absolute window maxima from capped slab clocks

The capped slab clock controls the coordinate in both directions: up to the `n`-th capped time
the absolute coordinate displacement is at most `n` slab radii. A uniform chance of surviving one
capped step therefore gives an exponential moment for the absolute coordinate maximum over a
time window, exactly as for the one-sided maximum.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- Every absolute coordinate displacement up to the `n`th capped time is at most `n` radii. -/
theorem abs_displacement_le_of_le_cappedSlabExitTime {d : ℕ} (γ : Path d) (i : Fin d)
    (r : ℝ) (hr : 0 < r) (g : ℝ≥0) (n : ℕ) (s : ℝ≥0)
    (hs : s ≤ cappedSlabExitTime γ i r g n) :
    |γ s i - γ 0 i| ≤ n * r := by
  induction n generalizing s with
  | zero =>
    have hs0 : s = 0 := le_antisymm (by simpa [cappedSlabExitTime_zero] using hs) zero_le
    simp [hs0]
  | succ n ih =>
    by_cases hle : s ≤ cappedSlabExitTime γ i r g n
    · have h := ih s hle
      have hnr : (n : ℝ) * r ≤ ((n + 1 : ℕ) : ℝ) * r := by
        apply mul_le_mul_of_nonneg_right _ hr.le
        exact_mod_cast Nat.le_succ n
      exact h.trans hnr
    · have hlo : cappedSlabExitTime γ i r g n ≤ s := (lt_of_not_ge hle).le
      have hstep := abs_sub_le_of_mem_cappedSlabStep γ i r hr g n s hlo hs
      have hprev := abs_cappedSlabExitTime_sub_le γ i r hr g n
      calc |γ s i - γ 0 i|
          ≤ |γ s i - γ (cappedSlabExitTime γ i r g n) i| +
            |γ (cappedSlabExitTime γ i r g n) i - γ 0 i| := abs_sub_le _ _ _
        _ ≤ r + n * r := add_le_add hstep hprev
        _ = ((n + 1 : ℕ) : ℝ) * r := by push_cast; ring

/-- The absolute coordinate maximum over a window is nonnegative. -/
theorem absoluteCoordinateMaximum_nonneg {d : ℕ} (i : Fin d) (g : ℝ≥0) (γ : Path d) :
    0 ≤ absoluteCoordinateMaximum i g γ := by
  have hf : Continuous fun u : ℝ≥0 => |γ u i - γ 0 i| := by fun_prop
  apply le_csSup (isCompact_Icc.image hf).bddAbove
  exact ⟨0, ⟨le_rfl, zero_le⟩, by simp⟩

/-- If the capped clock reaches the end of the window after `n` steps, the absolute window
maximum is at most `n` radii. -/
theorem absoluteCoordinateMaximum_le_of_le_cappedSlabExitTime {d : ℕ} (γ : Path d) (i : Fin d)
    (r : ℝ) (hr : 0 < r) (g : ℝ≥0) (n : ℕ) (hn : g ≤ cappedSlabExitTime γ i r g n) :
    absoluteCoordinateMaximum i g γ ≤ n * r := by
  apply csSup_le
  · exact ⟨_, ⟨0, ⟨le_rfl, zero_le⟩, rfl⟩⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact abs_displacement_le_of_le_cappedSlabExitTime γ i r hr g n s (hs.2.trans hn)

/-- A uniform positive chance of surviving one capped step gives an exponential moment for the
absolute window maximum, measured in slab radii. -/
theorem window_absolute_maximum_exponential_moment {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I)
    (i : Fin d) (r : ℝ) (hr : 0 < r) (g : ℝ≥0) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hsurv : ∀ y, ENNReal.ofReal ε ≤ K y {γ | g ≤ cappedCoordinateSlabExit γ i r g})
    (x : Vec d) :
    Integrable (fun γ : Path d => Real.exp ((ε / 4) * (absoluteCoordinateMaximum i g γ / r)))
        (K x) ∧
      (∫ γ, Real.exp ((ε / 4) * (absoluteCoordinateMaximum i g γ / r)) ∂K x) ≤
        Real.exp ε * Real.exp (ε / 4) / (1 - Real.exp (ε / 4 - ε / 2)) := by
  have hmeas : Measurable (fun γ : Path d => absoluteCoordinateMaximum i g γ / r) :=
    ((continuous_absoluteCoordinateMaximum i).measurable.comp
      (measurable_const.prodMk measurable_id)).div_const r
  apply exponential_moment_le_of_geometric_tail (K x) _ hmeas
    (fun γ => div_nonneg (absoluteCoordinateMaximum_nonneg i g γ) hr.le) ε hε hε1
  intro n
  have hsub : {γ : Path d | (n : ℝ) < absoluteCoordinateMaximum i g γ / r} ⊆
      {γ | cappedSlabExitTime γ i r g n < g} := by
    intro γ hγ
    by_contra hle
    have hge : g ≤ cappedSlabExitTime γ i r g n := le_of_not_gt hle
    have h := absoluteCoordinateMaximum_le_of_le_cappedSlabExitTime γ i r hr g n hge
    have h' : absoluteCoordinateMaximum i g γ / r ≤ n := by
      rw [div_le_iff₀ hr]
      exact h
    exact absurd hγ (not_lt.mpr h')
  exact (measure_mono hsub).trans
    (cappedSlabExitTime_lt_le_pow hd ω lam Λ hΛ hω K hfdd i r g ε hε.le hsurv x n)

end EinsteinFull.Regeneration
