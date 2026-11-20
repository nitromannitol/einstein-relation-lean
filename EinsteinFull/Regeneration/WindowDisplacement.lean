import EinsteinFull.Regeneration.CappedSlabRestart
import EinsteinFull.Regeneration.CappedSlabExitMeasurability
import EinsteinFull.Regeneration.GeometricTailMoment

/-!
# Window maxima from capped slab clocks

If the capped slab clock reaches the end of a time window after `n` steps, the
coordinate maximum over the window is at most `n` slab radii. When every capped
step lasts the whole horizon with a uniformly positive probability, the strong
Markov property makes the number of steps geometric, which gives an exponential
moment for the window maximum.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- Between successive capped slab times the coordinate stays within one radius. -/
theorem abs_sub_le_of_mem_cappedSlabStep {d : ℕ} (γ : Path d) (i : Fin d)
    (r : ℝ) (hr : 0 < r) (g : ℝ≥0) (n : ℕ) (t : ℝ≥0)
    (hlo : cappedSlabExitTime γ i r g n ≤ t)
    (hhi : t ≤ cappedSlabExitTime γ i r g (n + 1)) :
    |γ t i - γ (cappedSlabExitTime γ i r g n) i| ≤ r := by
  let s := cappedSlabExitTime γ i r g n
  let η := pathTimeShift γ s
  have hstep : t - s ≤ cappedCoordinateSlabExit η i r g := by
    apply tsub_le_iff_right.mpr
    simpa only [s, η, cappedSlabExitTime_succ, add_comm] using hhi
  have hcoord : |η (t - s) i - η 0 i| ≤ r := by
    by_cases hfin : coordinateSlabExit η i r = ⊤
    · have hstay := (MarkovProcess.ContinuousPath.exitTime_eq_top_iff
        (coordinateSlab i (η 0) r) η).mp hfin
      exact le_of_lt (hstay (t - s))
    · apply coordinate_slab_before_exit η i r hr hfin
      exact hstep.trans (by
        change cappedCoordinateSlabExit η i r g ≤ (coordinateSlabExit η i r).toNNReal
        simp only [cappedCoordinateSlabExit, hfin, ↓reduceIte, min_le_left])
  have hlo' : s ≤ t := hlo
  have hsum : s + (t - s) = t := add_tsub_cancel_of_le hlo'
  simpa only [η, pathTimeShift, ContinuousMap.coe_mk, add_zero, hsum] using hcoord

/-- After `n` capped steps the coordinate has moved by at most `n` radii. -/
theorem abs_cappedSlabExitTime_sub_le {d : ℕ} (γ : Path d) (i : Fin d)
    (r : ℝ) (hr : 0 < r) (g : ℝ≥0) (n : ℕ) :
    |γ (cappedSlabExitTime γ i r g n) i - γ 0 i| ≤ n * r := by
  induction n with
  | zero => simp [cappedSlabExitTime_zero]
  | succ n ih =>
    have hstep := capped_slab_exit_step_bound γ i r hr g n
    calc |γ (cappedSlabExitTime γ i r g (n + 1)) i - γ 0 i|
        ≤ |γ (cappedSlabExitTime γ i r g (n + 1)) i - γ (cappedSlabExitTime γ i r g n) i| +
          |γ (cappedSlabExitTime γ i r g n) i - γ 0 i| := abs_sub_le _ _ _
      _ ≤ r + n * r := add_le_add hstep ih
      _ = ((n + 1 : ℕ) : ℝ) * r := by push_cast; ring

/-- Every coordinate displacement up to the `n`th capped time is at most `n` radii. -/
theorem displacement_le_of_le_cappedSlabExitTime {d : ℕ} (γ : Path d) (i : Fin d)
    (r : ℝ) (hr : 0 < r) (g : ℝ≥0) (n : ℕ) (s : ℝ≥0)
    (hs : s ≤ cappedSlabExitTime γ i r g n) :
    γ s i - γ 0 i ≤ n * r := by
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
      have h1 := (abs_le.mp hstep).2
      have h2 := (abs_le.mp hprev).2
      push_cast
      linarith

/-- If the capped clock reaches the end of the window after `n` steps, the window
maximum is at most `n` radii. -/
theorem coordinateMaximum_le_of_le_cappedSlabExitTime {d : ℕ} (γ : Path d) (i : Fin d)
    (r : ℝ) (hr : 0 < r) (g : ℝ≥0) (n : ℕ) (hn : g ≤ cappedSlabExitTime γ i r g n) :
    coordinateMaximum γ i g ≤ n * r := by
  apply coordinateMaximum_le
  intro s hs
  exact displacement_le_of_le_cappedSlabExitTime γ i r hr g n s (hs.2.trans hn)

/-- If each capped step lasts the whole horizon with probability at least `ε` from
every start, the capped clock stays below the horizon for `n` steps with
probability at most `(1 - ε)ⁿ`. -/
theorem cappedSlabExitTime_lt_le_pow {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I)
    (i : Fin d) (r : ℝ) (g : ℝ≥0) (ε : ℝ) (hε : 0 ≤ ε)
    (hsurv : ∀ y, ENNReal.ofReal ε ≤ K y {γ | g ≤ cappedCoordinateSlabExit γ i r g})
    (x : Vec d) (n : ℕ) :
    K x {γ | cappedSlabExitTime γ i r g n < g} ≤ ENNReal.ofReal (1 - ε) ^ n := by
  induction n with
  | zero => simpa using prob_le_one
  | succ n ih =>
    let T : Path d → ℝ≥0 := fun γ => cappedSlabExitTime γ i r g n
    have hT := isStoppingTime_cappedSlabExitTime i r g n
    let A : Set (Path d) := {γ | T γ < g}
    have hA : MeasurableSet[hT.measurableSpace] A := by
      have h := hT.measurableSet_lt' g
      have heq : {γ : Path d | ((T γ : ℝ≥0) : ℝ≥0∞) < ((g : ℝ≥0) : WithTop ℝ≥0)} = A := by
        ext γ
        exact ENNReal.coe_lt_coe
      rw [← heq]
      exact h
    let B : Set (Path d) := {γ | cappedCoordinateSlabExit γ i r g < g}
    have hB : MeasurableSet B :=
      measurableSet_lt (measurable_cappedCoordinateSlabExit i r g) measurable_const
    let S : Path d → Path d := fun γ => MarkovProcess.ContinuousPath.shift (T γ) γ
    have hS : Measurable S := MarkovProcess.ContinuousPath.measurable_shift_stoppingTime T hT
    have hshift (γ : Path d) : S γ = pathTimeShift γ (T γ) := by
      ext t
      rfl
    have hsub : {γ : Path d | cappedSlabExitTime γ i r g (n + 1) < g} ⊆ A ∩ S ⁻¹' B := by
      intro γ hγ
      have hγ' : T γ + cappedCoordinateSlabExit (pathTimeShift γ (T γ)) i r g < g := by
        simpa only [T, cappedSlabExitTime_succ, Set.mem_ofPred_eq] using hγ
      refine ⟨lt_of_le_of_lt (le_add_of_nonneg_right zero_le) hγ', ?_⟩
      change cappedCoordinateSlabExit (S γ) i r g < g
      rw [hshift]
      exact lt_of_le_of_lt (le_add_of_nonneg_left zero_le) hγ'
    have hstepB (y : Vec d) : K y B ≤ ENNReal.ofReal (1 - ε) := by
      have hc : Bᶜ = {γ : Path d | g ≤ cappedCoordinateSlabExit γ i r g} := by
        ext γ
        simp [B]
      have hcompl := prob_compl_eq_one_sub (μ := K y) hB
      rw [hc] at hcompl
      have h := hsurv y
      rw [ENNReal.ofReal_sub _ hε, ENNReal.ofReal_one]
      calc K y B = 1 - (1 - K y B) := by
            rw [ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one]
        _ = 1 - K y {γ | g ≤ cappedCoordinateSlabExit γ i r g} := by rw [hcompl]
        _ ≤ 1 - ENNReal.ofReal ε := tsub_le_tsub_left h 1
    have hrestart := u1_regular_signed_realization_stopping_restart hd ω lam Λ hΛ hω K hfdd x
      T hT A hA
    calc K x {γ | cappedSlabExitTime γ i r g (n + 1) < g}
        ≤ K x (S ⁻¹' B ∩ A) := by
          rw [Set.inter_comm]
          exact measure_mono hsub
      _ = ((K x).restrict A).map S B := by
          rw [Measure.map_apply hS hB, Measure.restrict_apply (hS hB)]
      _ = ∫⁻ γ, K (γ (T γ)) B ∂((K x).restrict A) := by
          rw [hrestart, Measure.bind_apply hB (Kernel.aemeasurable _)]
          rfl
      _ ≤ ∫⁻ _γ, ENNReal.ofReal (1 - ε) ∂((K x).restrict A) :=
          lintegral_mono fun γ => hstepB _
      _ = ENNReal.ofReal (1 - ε) * K x A := by
          rw [lintegral_const, Measure.restrict_apply_univ]
      _ ≤ ENNReal.ofReal (1 - ε) * ENNReal.ofReal (1 - ε) ^ n := by gcongr
      _ = ENNReal.ofReal (1 - ε) ^ (n + 1) := by rw [pow_succ, mul_comm]

/-- A uniform positive chance of surviving one capped step gives an exponential
moment for the window maximum, measured in slab radii. -/
theorem window_maximum_exponential_moment {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I)
    (i : Fin d) (r : ℝ) (hr : 0 < r) (g : ℝ≥0) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hsurv : ∀ y, ENNReal.ofReal ε ≤ K y {γ | g ≤ cappedCoordinateSlabExit γ i r g})
    (x : Vec d) :
    Integrable (fun γ : Path d => Real.exp ((ε / 4) * (coordinateMaximum γ i g / r))) (K x) ∧
      (∫ γ, Real.exp ((ε / 4) * (coordinateMaximum γ i g / r)) ∂K x) ≤
        Real.exp ε * Real.exp (ε / 4) / (1 - Real.exp (ε / 4 - ε / 2)) := by
  have hmeas : Measurable (fun γ : Path d => coordinateMaximum γ i g / r) :=
    ((measurable_coordinateMaximum i).comp (measurable_const.prodMk measurable_id)).div_const r
  apply exponential_moment_le_of_geometric_tail (K x) _ hmeas
    (fun γ => div_nonneg (coordinateMaximum_nonneg γ i g) hr.le) ε hε hε1
  intro n
  have hsub : {γ : Path d | (n : ℝ) < coordinateMaximum γ i g / r} ⊆
      {γ | cappedSlabExitTime γ i r g n < g} := by
    intro γ hγ
    by_contra hle
    have hge : g ≤ cappedSlabExitTime γ i r g n := le_of_not_gt hle
    have h := coordinateMaximum_le_of_le_cappedSlabExitTime γ i r hr g n hge
    have h' : coordinateMaximum γ i g / r ≤ n := by
      rw [div_le_iff₀ hr]
      exact h
    exact absurd hγ (not_lt.mpr h')
  exact (measure_mono hsub).trans
    (cappedSlabExitTime_lt_le_pow hd ω lam Λ hΛ hω K hfdd i r g ε hε.le hsurv x n)

end EinsteinFull.Regeneration
