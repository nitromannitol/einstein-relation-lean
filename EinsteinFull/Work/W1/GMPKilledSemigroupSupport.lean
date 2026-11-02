import EinsteinFull.Work.W1.GMPFullPastRestartSupport
import EinsteinFull.Work.W1.GMPKilledContinuitySupport
import Mathlib.Probability.Kernel.Composition.CompMap

/-!
# The actual GMP semigroup killed on exit from an open set

Strict survival is an event of the full deterministic past. Actual path-law
restart therefore gives the killed endpoint semigroup at every starting point.
Its literal physical L² realizations inherit the semigroup law and strong
continuity. These results do not identify the killed evolution with the
variational zero-boundary evolution.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal Topology
namespace EinsteinFull
open EinsteinRelation EinsteinRelation.Diffusion
open EinsteinRelation.External.GantertSection7Support
noncomputable section

/-- Strict survival through a deterministic time depends on the complete prefix. -/
theorem localitySurvival_prefix {d : ℕ} (U : Set (Vec d)) (hU : IsOpen U)
    (s : ℝ≥0) :
    (gmpPrefixPath s) ⁻¹' {γ : Path d | (s : ℝ≥0∞) < localityExitTime U γ} =
      {γ : Path d | (s : ℝ≥0∞) < localityExitTime U γ} := by
  ext γ
  simp only [Set.mem_preimage, Set.mem_setOf_eq, lt_localityExitTime_iff U hU]
  constructor
  · intro h t ht
    simpa only [gmpPrefixPath, ContinuousMap.coe_mk, min_eq_left ht] using h t ht
  · intro h t ht
    exact h (min t s) (min_le_right _ _)

/-- The literal strict-survival event belongs to the full natural past sigma-algebra. -/
theorem measurableSet_localitySurvival_past {d : ℕ} (U : Set (Vec d)) (hU : IsOpen U)
    (s : ℝ≥0) :
    MeasurableSet[gmpPastSigma s] {γ : Path d | (s : ℝ≥0∞) < localityExitTime U γ} := by
  rw [← comap_gmpPrefixPath_eq_gmpPastSigma]
  exact ⟨_, measurableSet_localitySurvival U hU s, localitySurvival_prefix U hU s⟩

/-- Survival on a concatenated interval splits into survival of the prefix
and survival of the actual shifted path, with strict exit-time conventions. -/
theorem localitySurvival_add {d : ℕ} (U : Set (Vec d)) (hU : IsOpen U)
    (s t : ℝ≥0) :
    {γ : Path d | ((s + t : ℝ≥0) : ℝ≥0∞) < localityExitTime U γ} =
      (gmpShiftPath s) ⁻¹' {γ : Path d | (t : ℝ≥0∞) < localityExitTime U γ} ∩
        {γ : Path d | (s : ℝ≥0∞) < localityExitTime U γ} := by
  ext γ
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq,
    lt_localityExitTime_iff U hU]
  constructor
  · intro h
    constructor
    · intro u hu
      exact h (s + u) (add_le_add_right hu s)
    · intro u hu
      exact h u (hu.trans (le_add_of_nonneg_right zero_le))
  · rintro ⟨hfuture, hpast⟩ u hu
    by_cases hs : u ≤ s
    · exact hpast u hs
    · have hsu : s ≤ u := le_of_lt (lt_of_not_ge hs)
      have hv : u - s ≤ t := tsub_le_iff_right.mpr (by simpa only [add_comm] using hu)
      have h := hfuture (u - s) hv
      simpa only [gmpShiftPath, ContinuousMap.coe_mk, add_tsub_cancel_of_le hsu] using h

variable {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L} {ω : FieldPair d}
  {hω : IsRegular L ω} {lam : ℝ} {h₀ : 0 ≤ lam} {h₁ : lam ≤ 1}
  (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁)

/-- Restart after strict survival uses the actual killed endpoint distribution,
at every starting point and for the complete shifted path law. -/
theorem gmpPathLaw_restrict_survival_map_shift (U : Set (Vec d)) (hU : IsOpen U)
    (s : ℝ≥0) :
    (G.pathLaw.restrict (measurableSet_localitySurvival U hU s)).map (gmpShiftPath s) =
      G.pathLaw ∘ₖ gmpKilledEndpointKernel G U hU s :=
  gmpPathLaw_restrict_past_map_shift G s _ (measurableSet_localitySurvival_past U hU s)

/-- The actual kernels killed on exit form a semigroup for every open domain,
including unbounded and empty domains, with no exceptional starting points. -/
theorem gmpKilledEndpointKernel_add (U : Set (Vec d)) (hU : IsOpen U) (s t : ℝ≥0) :
    gmpKilledEndpointKernel G U hU (s + t) =
      gmpKilledEndpointKernel G U hU t ∘ₖ gmpKilledEndpointKernel G U hU s := by
  letI := G.pathLaw_isMarkovKernel
  letI := isFiniteKernel_gmpKilledEndpointKernel G U hU s
  have h := congrArg (fun κ : Kernel (Vec d) (Path d) =>
      (κ.restrict (measurableSet_localitySurvival U hU t)).map (pathPosition t))
    (gmpPathLaw_restrict_survival_map_shift G U hU s)
  rw [← Kernel.comp_restrict, Kernel.map_comp] at h
  change _ = gmpKilledEndpointKernel G U hU t ∘ₖ gmpKilledEndpointKernel G U hU s at h
  rw [← h]
  apply Kernel.ext
  intro x
  rw [gmpKilledEndpointKernel_apply,
    Kernel.map_apply _ (measurable_pathPosition _), Kernel.restrict_apply,
    Kernel.map_apply _ (measurable_gmpShiftPath _),
    Measure.restrict_map (measurable_gmpShiftPath _) (measurableSet_localitySurvival U hU t),
    Measure.map_map (measurable_pathPosition _) (measurable_gmpShiftPath _),
    Kernel.restrict_apply, Measure.restrict_restrict
      ((measurableSet_localitySurvival U hU t).preimage (measurable_gmpShiftPath _)),
    ← localitySurvival_add U hU s t]
  congr 1

/-- The actual physical L² killed expectations compose in time on all ambient data. -/
theorem gmpKilledL2_add_time (U : Set (Vec d)) (hU : IsOpen U) (s t : ℝ≥0)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    gmpKilledL2 G U hU (s + t) f =
      gmpKilledL2 G U hU s (gmpKilledL2 G U hU t f) := by
  letI := isFiniteKernel_gmpKilledEndpointKernel G U hU s
  letI := isFiniteKernel_gmpKilledEndpointKernel G U hU t
  letI := isFiniteKernel_gmpKilledEndpointKernel G U hU (s + t)
  apply Lp.ext
  filter_upwards [gmpKilledL2_ae_eq G U hU (s + t) f,
    gmpKilledL2_ae_eq G U hU s (gmpKilledL2 G U hU t f),
    ae_ae_gmpKilledEndpointKernel_of_ae G U hU s (gmpKilledL2_ae_eq G U hU t f),
    ae_memLp_gmpKilledEndpointKernel G U hU (s + t) f]
    with x hx hy ht hf
  rw [hx, hy]
  have hi := hf.integrable (by norm_num)
  rw [gmpKilledEndpointKernel_add G U hU s t] at hi ⊢
  rw [Kernel.integral_comp hi]
  exact integral_congr_ae (Filter.EventuallyEq.symm ht)

/-- The actual killed bounded operators satisfy the semigroup law on physical L². -/
theorem gmpKilledL2Operator_add_time (U : Set (Vec d)) (hU : IsOpen U) (s t : ℝ≥0) :
    gmpKilledL2Operator G U hU (s + t) =
      (gmpKilledL2Operator G U hU s).comp (gmpKilledL2Operator G U hU t) := by
  apply ContinuousLinearMap.ext
  intro f
  exact gmpKilledL2_add_time G U hU s t f

/-- The actual killed operators form a semigroup on the exact physical interior carrier. -/
theorem gmpKilledInteriorOperator_add_time (U : Set (Vec d)) (hU : IsOpen U) (s t : ℝ≥0) :
    gmpKilledInteriorOperator G U hU (s + t) =
      (gmpKilledInteriorOperator G U hU s).comp (gmpKilledInteriorOperator G U hU t) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  exact gmpKilledL2_add_time G U hU s t f.val

private theorem norm_gmpKilledInteriorOperator_sub_le (U : Set (Vec d)) (hU : IsOpen U)
    (f : physicalZeroBoundaryL2 U hd ω lam L hω) (s t : ℝ≥0) (hst : s ≤ t) :
    ‖gmpKilledInteriorOperator G U hU t f - gmpKilledInteriorOperator G U hU s f‖ ≤
      ‖gmpKilledInteriorOperator G U hU (t - s) f - f‖ := by
  have he : gmpKilledInteriorOperator G U hU t f - gmpKilledInteriorOperator G U hU s f =
      gmpKilledInteriorOperator G U hU s (gmpKilledInteriorOperator G U hU (t - s) f - f) := by
    rw [map_sub, ← ContinuousLinearMap.comp_apply,
      ← gmpKilledInteriorOperator_add_time, add_tsub_cancel_of_le hst]
  rw [he]
  exact gmpKilledInteriorOperator_norm_le G U hU s _

/-- The actual killed interior semigroup is strongly continuous at every time. -/
theorem continuous_gmpKilledInteriorOperator_apply (U : Set (Vec d)) (hU : IsOpen U)
    (f : physicalZeroBoundaryL2 U hd ω lam L hω) :
    Continuous (fun t : ℝ≥0 => gmpKilledInteriorOperator G U hU t f) := by
  have hc : ContinuousAt (fun t : ℝ≥0 => gmpKilledInteriorOperator G U hU t f) 0 := by
    change Tendsto (fun t : ℝ≥0 => gmpKilledInteriorOperator G U hU t f) (𝓝 0)
      (𝓝 (gmpKilledInteriorOperator G U hU 0 f))
    rw [gmpKilledInteriorOperator_zero]
    exact tendsto_gmpKilledInteriorOperator_at_zero G U hU f
  apply continuous_iff_continuousAt.mpr
  intro t
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := Metric.continuousAt_iff.mp hc ε hε
  refine ⟨δ, hδ, fun s hs => ?_⟩
  have hsmall (a b : ℝ≥0) (hab : a ≤ b) : dist (b - a) 0 = dist b a := by
    rw [NNReal.dist_eq, NNReal.coe_sub hab, NNReal.coe_zero, sub_zero, NNReal.dist_eq]
  rcases le_total s t with hst | hts
  · have hh := hmod (show dist (t - s) 0 < δ by rw [hsmall s t hst, dist_comm]; exact hs)
    rw [gmpKilledInteriorOperator_zero, dist_eq_norm] at hh
    rw [dist_eq_norm, norm_sub_rev]
    exact (norm_gmpKilledInteriorOperator_sub_le G U hU f s t hst).trans_lt hh
  · have hh := hmod (show dist (s - t) 0 < δ by rw [hsmall t s hts]; exact hs)
    rw [gmpKilledInteriorOperator_zero, dist_eq_norm] at hh
    rw [dist_eq_norm]
    exact (norm_gmpKilledInteriorOperator_sub_le G U hU f t s hts).trans_lt hh

/-- Ambient killed physical L² orbits are continuous, including their projected value at zero. -/
theorem continuous_gmpKilledL2_apply (U : Set (Vec d)) (hU : IsOpen U)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    Continuous (fun t : ℝ≥0 => gmpKilledL2 G U hU t f) := by
  have h := (physicalZeroBoundaryL2 U hd ω lam L hω).subtypeL.continuous.comp
    (continuous_gmpKilledInteriorOperator_apply G U hU
      ⟨physicalZeroBoundaryProjection U hd ω lam L hω f,
        physicalZeroBoundaryProjection_mem U hd ω lam L hω f⟩)
  change Continuous (fun t : ℝ≥0 => gmpKilledL2 G U hU t
    (physicalZeroBoundaryProjection U hd ω lam L hω f)) at h
  simpa only [gmpKilledL2_projection] using h

end
end EinsteinFull
