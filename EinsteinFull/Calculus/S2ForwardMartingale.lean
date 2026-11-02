import EinsteinFull.Calculus.S4TimeChangeMartingale
import EinsteinFull.Calculus.S2ForwardClockSupport

/-!
# The forward time change of a physical solution solves the reduced martingale problem

For a smooth regular environment `ω`, if `PX` solves the physical martingale problem from `x`,
then the image of `PX` under the forward map `γ ↦ γ ∘ A⁻¹` (inverse clock of the sign-flipped
potential, density `exp (2 ω.2)`) solves the reduced martingale problem from `x`.  The proof is
optional stopping of the physical compensated test at the bounded stopping times
`τ_s = A_γ⁻¹ (s)`: the substitution `u = A_γ (t)` shows that the reduced compensated test of the
time-changed path at time `s` is the physical compensated test of `γ` at time `τ_s`.
-/

open MeasureTheory
open scoped NNReal

namespace EinsteinFull
open EinsteinRelation
open EinsteinRelation.Clock EinsteinRelation.Clock.InverseMeaningV3

theorem clockDensity_mul_clockDensity_flip {d : ℕ} (ω : FieldPair d) (x : Vec d) :
    clockDensity ω x * clockDensity (flipPotential ω) x = 1 := by
  rw [clockDensity, clockDensity, ← Real.exp_add, flipPotential_apply,
    show -2 * ω.2 x + -2 * -ω.2 x = 0 by ring, Real.exp_zero]

/-- The reduced compensated test along the forward time change is the physical compensated test
at the stopping time `τ_s`. -/
theorem compensatedTest_reduced_forwardClockPath {d : ℕ} {L : ℝ} {ω : FieldPair d}
    (hω : IsRegular L ω) (hs : IsSmoothFieldPair ω) (i : Fin d) (lam : ℝ) {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (γ : Path d) (s : ℝ≥0) :
    compensatedTest (reducedGenerator i ω lam) f s (forwardClockPath hω γ) =
      compensatedTest (physicalGenerator i ω lam) f
        (inversePhysicalPathClock (flipPotential ω) γ L (isRegular_flipPotential hω) s) γ := by
  have hω' := isRegular_flipPotential hω
  unfold compensatedTest
  have h0 : forwardClockPath hω γ 0 = γ 0 := forwardClockPath_zero hω γ
  have hcv := timeChange_integral hω' γ s
    (G := reducedGenerator i ω lam f) (continuous_reducedGenerator_apply hs i lam hf)
  have e1 : (fun t : ℝ => reducedGenerator i ω lam f (γ t.toNNReal) *
      clockDensity (flipPotential ω) (γ t.toNNReal)) =
      fun t : ℝ => physicalGenerator i ω lam f (γ t.toNNReal) := by
    funext t
    rw [← clockDensity_mul_physicalGenerator]
    calc clockDensity ω (γ t.toNNReal) * physicalGenerator i ω lam f (γ t.toNNReal) *
          clockDensity (flipPotential ω) (γ t.toNNReal)
        = (clockDensity ω (γ t.toNNReal) * clockDensity (flipPotential ω) (γ t.toNNReal)) *
            physicalGenerator i ω lam f (γ t.toNNReal) := by ring
      _ = _ := by rw [clockDensity_mul_clockDensity_flip, one_mul]
  have e2 : ∫ t in (0 : ℝ)..((inversePhysicalPathClock (flipPotential ω) γ L hω' s : ℝ≥0) : ℝ),
        physicalGenerator i ω lam f (γ t.toNNReal) =
      ∫ u in (0 : ℝ)..(s : ℝ), reducedGenerator i ω lam f (forwardClockPath hω γ u.toNNReal) := by
    rw [← e1]
    exact hcv
  rw [h0, ← e2]
  rfl

theorem forwardClock_solves {d : ℕ} {L : ℝ} (hL : 0 < L) {ω : FieldPair d}
    (hω : IsRegular L ω) (hs : IsSmoothFieldPair ω) (i : Fin d) (lam : ℝ) (x : Vec d)
    {PX : Measure (Path d)}
    (hX : SolvesMartingaleProblem (physicalGenerator i ω lam) x PX) :
    SolvesMartingaleProblem (reducedGenerator i ω lam) x (PX.map (forwardClockPath hω)) := by
  have hω' := isRegular_flipPotential hω
  obtain ⟨hprob, hstart, hf⟩ := hX
  have : IsProbabilityMeasure PX := hprob
  have hΦ : Measurable (forwardClockPath hω) := measurable_forwardClockPath hω
  refine ⟨inferInstance, ?_, ?_⟩
  · have hmeas : MeasurableSet {γ : Path d | γ 0 = x} :=
      (measurable_pathPosition 0) (measurableSet_singleton x)
    rw [ae_map_iff hΦ.aemeasurable hmeas]
    filter_upwards [hstart] with γ hγ
    show forwardClockPath hω γ 0 = x
    rw [forwardClockPath_zero]
    exact hγ
  · intro f hfs hfc
    obtain ⟨_, _, hmart⟩ := hf f hfs hfc
    have hf0 : Continuous f := hfs.continuous
    obtain ⟨Cf, hCf⟩ : ∃ Cf : ℝ, ∀ y, |f y| ≤ Cf := by
      obtain ⟨C, hC⟩ := hf0.bounded_above_of_compact_support hfc
      exact ⟨C, fun y => by
        have := hC y
        rwa [Real.norm_eq_abs] at this⟩
    have hLr := continuous_reducedGenerator_apply hs i lam hfs
    have hLp := continuous_physicalGenerator_apply hs i lam hfs
    obtain ⟨Cr, hCr⟩ := bounded_reducedGenerator_apply hL hω hs i lam hfs hfc
    obtain ⟨Cp, hCp⟩ := bounded_physicalGenerator_apply hL hω hs i lam hfs hfc
    have hNad := stronglyAdapted_compensatedTest (reducedGenerator i ω lam) f hf0 hLr
    have hNint : ∀ t : ℝ≥0, Integrable (compensatedTest (reducedGenerator i ω lam) f t)
        (PX.map (forwardClockPath hω)) := by
      intro t
      have hm : StronglyMeasurable (compensatedTest (reducedGenerator i ω lam) f t) :=
        (hNad t).mono ((pathFiltration d).le t)
      exact Integrable.of_bound hm.aestronglyMeasurable (2 * Cf + Cr * t)
        (Filter.Eventually.of_forall fun γ => norm_compensatedTest_le _ f hCf hCr t γ)
    refine ⟨fun t => Filter.Eventually.of_forall fun γ => ?_, hNint, ?_⟩
    · exact (hLr.comp (γ.continuous.comp continuous_real_toNNReal)).intervalIntegrable _ _
    · rw [pathFiltration_eq_canonical] at hmart ⊢
      rw [pathFiltration_eq_canonical] at hNad
      refine ⟨hNad, fun r s hrs => ?_⟩
      have hNm : ∀ t : ℝ≥0, StronglyMeasurable
          (compensatedTest (reducedGenerator i ω lam) f t) := fun t =>
        (hNad t).mono ((MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d)).le t)
      refine (ae_eq_condExp_of_forall_setIntegral_eq
        ((MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d)).le r)
        (hNint s) (fun B _ _ => (hNint r).integrableOn) ?_
        (hNad r).aestronglyMeasurable).symm
      intro B hB _
      have hBm : MeasurableSet B :=
        (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d)).le r B hB
      rw [setIntegral_map hBm (hNm r).aestronglyMeasurable hΦ.aemeasurable,
        setIntegral_map hBm (hNm s).aestronglyMeasurable hΦ.aemeasurable]
      have e : ∀ (t : ℝ≥0) (γ : Path d),
          compensatedTest (reducedGenerator i ω lam) f t (forwardClockPath hω γ) =
            compensatedTest (physicalGenerator i ω lam) f
              (inversePhysicalPathClock (flipPotential ω) γ L hω' t) γ := fun t γ =>
        compensatedTest_reduced_forwardClockPath hω hs i lam hfs γ t
      have hint' : ∀ t : ℝ≥0, Integrable (fun γ : Path d =>
          compensatedTest (physicalGenerator i ω lam) f
            (inversePhysicalPathClock (flipPotential ω) γ L hω' t) γ) PX := by
        intro t
        have h1 := (integrable_map_measure (hNm t).aestronglyMeasurable
          hΦ.aemeasurable).1 (hNint t)
        have e' : (fun γ : Path d => compensatedTest (physicalGenerator i ω lam) f
            (inversePhysicalPathClock (flipPotential ω) γ L hω' t) γ) =
            compensatedTest (reducedGenerator i ω lam) f t ∘ forwardClockPath hω :=
          funext fun γ => (e t γ).symm
        rw [e']
        exact h1
      have hbound : ∀ v : ℝ≥0, ∃ C : ℝ, ∀ t ≤ v, ∀ γ : Path d,
          ‖compensatedTest (physicalGenerator i ω lam) f t γ‖ ≤ C := by
        intro v
        refine ⟨2 * Cf + max Cp 0 * v, fun t ht γ => ?_⟩
        have h := norm_compensatedTest_le (physicalGenerator i ω lam) f (CL := max Cp 0) hCf
          (fun y => (hCp y).trans (le_max_left _ _)) t γ
        have h' : max Cp 0 * (t : ℝ) ≤ max Cp 0 * v :=
          mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.2 ht) (le_max_right _ _)
        linarith
      have hright : ∀ (γ : Path d) (v : ℝ≥0),
          ContinuousWithinAt (fun t : ℝ≥0 => compensatedTest (physicalGenerator i ω lam) f t γ)
            (Set.Ici v) v := fun γ v =>
        (continuous_compensatedTest_time _ f hf0 hLp γ).continuousWithinAt
      have hmono : ∀ γ : Path d, inversePhysicalPathClock (flipPotential ω) γ L hω' r ≤
          inversePhysicalPathClock (flipPotential ω) γ L hω' s := fun γ =>
        (physicalPathClockOrderIso (flipPotential ω) γ L hω').symm.monotone hrs
      have hsK : ∀ γ : Path d, inversePhysicalPathClock (flipPotential ω) γ L hω' s ≤
          Real.toNNReal (Real.exp (2 * L) * s) := fun γ =>
        NNReal.le_toNNReal_of_coe_le (inversePhysicalPathClock_bounds (flipPotential ω) γ L hω' s).2
      have hB' : MeasurableSet[(isStoppingTime_inversePhysicalPathClock_canonical hω' r).measurableSpace]
          (forwardClockPath hω ⁻¹' B) :=
        measurable_timeChangeMap_stopped hω' r hB
      have key := setIntegral_stoppedValue_eq (μ := PX) hmart hbound hright
        (isStoppingTime_inversePhysicalPathClock_canonical hω' r)
        (isStoppingTime_inversePhysicalPathClock_canonical hω' s) hmono
        (fun γ => (hmono γ).trans (hsK γ)) hsK (hint' r) (hint' s) hB'
      have lhs : ∫ x in forwardClockPath hω ⁻¹' B,
          compensatedTest (reducedGenerator i ω lam) f r (forwardClockPath hω x) ∂PX =
          ∫ x in forwardClockPath hω ⁻¹' B, compensatedTest (physicalGenerator i ω lam) f
            (inversePhysicalPathClock (flipPotential ω) x L hω' r) x ∂PX :=
        setIntegral_congr_fun (hΦ hBm) fun γ _ => e r γ
      have rhs : ∫ x in forwardClockPath hω ⁻¹' B,
          compensatedTest (reducedGenerator i ω lam) f s (forwardClockPath hω x) ∂PX =
          ∫ x in forwardClockPath hω ⁻¹' B, compensatedTest (physicalGenerator i ω lam) f
            (inversePhysicalPathClock (flipPotential ω) x L hω' s) x ∂PX :=
        setIntegral_congr_fun (hΦ hBm) fun γ _ => e s γ
      rw [lhs, rhs]
      exact key.symm

end EinsteinFull
