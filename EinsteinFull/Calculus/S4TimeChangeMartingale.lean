import EinsteinFull.Calculus.S4TimeChangeSupport
import EinsteinFull.Calculus.S4OptionalStoppingSupport

/-!
# The inverse-clock image of a reduced solution solves the physical martingale problem

For a smooth regular environment, if `PY` solves the reduced martingale problem from `x`, then
the image of `PY` under `γ ↦ inverseClockPath ω γ` solves the physical martingale problem from
`x`.  The proof is the optional stopping argument at the bounded stopping times
`σ_s = A_γ⁻¹ (s)`: the compensated physical test at time `s` is the compensated reduced test at
`σ_s` (deterministic change of variables), and the compensated reduced test is a locally bounded
continuous martingale.
-/

open MeasureTheory
open scoped NNReal

namespace EinsteinFull
open EinsteinRelation
open EinsteinRelation.Clock EinsteinRelation.Clock.InverseMeaningV3

/-- The path map `γ ↦ inverseClockPath ω γ`. -/
noncomputable def timeChangeMap {d : ℕ} {L : ℝ} {ω : FieldPair d} (hω : IsRegular L ω)
    (γ : Path d) : Path d :=
  inverseClockPath ω γ L hω

theorem measurable_timeChangeMap {d : ℕ} {L : ℝ} {ω : FieldPair d} (hω : IsRegular L ω) :
    Measurable (timeChangeMap hω) :=
  (Clock.PathMapV4.measurable_inverseClockPathMap (d := d) (L := L)).comp
    ((measurable_const (a := (⟨ω, hω⟩ : Clock.PathMapV4.PhysicalInput d L))).prodMk
      measurable_id)

theorem norm_compensatedTest_le {d : ℕ} (L : (Vec d → ℝ) → Vec d → ℝ) (f : Vec d → ℝ)
    {Cf CL : ℝ} (hf : ∀ y, |f y| ≤ Cf) (hL : ∀ y, |L f y| ≤ CL) (t : ℝ≥0) (γ : Path d) :
    ‖compensatedTest L f t γ‖ ≤ 2 * Cf + CL * t := by
  unfold compensatedTest
  have hint : ‖∫ u in (0 : ℝ)..(t : ℝ), L f (γ u.toNNReal)‖ ≤ CL * |(t : ℝ) - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun u _ => by
      rw [Real.norm_eq_abs]
      exact hL _
  rw [sub_zero, abs_of_nonneg t.coe_nonneg] at hint
  have h1 : ‖f (γ t)‖ ≤ Cf := by
    rw [Real.norm_eq_abs]
    exact hf _
  have h2 : ‖f (γ 0)‖ ≤ Cf := by
    rw [Real.norm_eq_abs]
    exact hf _
  have h3 := norm_sub_le (f (γ t) - f (γ 0)) (∫ u in (0 : ℝ)..(t : ℝ), L f (γ u.toNNReal))
  have h4 := norm_sub_le (f (γ t)) (f (γ 0))
  linarith

theorem continuous_compensatedTest_time {d : ℕ} (L : (Vec d → ℝ) → Vec d → ℝ) (f : Vec d → ℝ)
    (hf : Continuous f) (hLc : Continuous (L f)) (γ : Path d) :
    Continuous fun t : ℝ≥0 => compensatedTest L f t γ := by
  unfold compensatedTest
  have hI : Continuous fun t : ℝ≥0 => ∫ u in (0 : ℝ)..(t : ℝ), L f (γ u.toNNReal) :=
    (intervalIntegral.continuous_primitive
      (fun a b => (hLc.comp (γ.continuous.comp continuous_real_toNNReal)).intervalIntegrable a b)
      0).comp NNReal.continuous_coe
  have hγ : Continuous fun t : ℝ≥0 => f (γ t) := hf.comp γ.continuous
  first
    | exact (hγ.sub continuous_const).sub hI
    | fun_prop

theorem isStoppingTime_inversePhysicalPathClock_canonical {d : ℕ} {L : ℝ} {ω : FieldPair d}
    (hω : IsRegular L ω) (s : ℝ≥0) :
    IsStoppingTime (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d))
      (fun γ : Path d => ((inversePhysicalPathClock ω γ L hω s : ℝ≥0) : WithTop ℝ≥0)) := by
  have h := isStoppingTime_inversePhysicalPathClock hω s
  rw [pathFiltration_eq_canonical] at h
  exact h

theorem measurable_timeChangeMap_stopped {d : ℕ} {L : ℝ} {ω : FieldPair d}
    (hω : IsRegular L ω) (r : ℝ≥0) :
    Measurable[(isStoppingTime_inversePhysicalPathClock_canonical hω r).measurableSpace,
      MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d) r]
      (timeChangeMap hω) := by
  refine Measurable.of_comap_le ?_
  change MeasurableSpace.comap (timeChangeMap hω) (⨆ s : Set.Iic r,
    MeasurableSpace.comap (MarkovProcess.ContinuousPath.coordinateProcess (alpha := Vec d) s)
      inferInstance) ≤ _
  rw [MeasurableSpace.comap_iSup]
  refine iSup_le fun j => ?_
  rw [MeasurableSpace.comap_comp]
  have hjr : j.1 ≤ r := Set.mem_Iic.1 j.2
  have hj := MarkovProcess.ContinuousPath.measurable_eval_stoppingTime (alpha := Vec d)
    (fun γ => inversePhysicalPathClock ω γ L hω j.1)
    (isStoppingTime_inversePhysicalPathClock_canonical hω j.1)
  have hle : (isStoppingTime_inversePhysicalPathClock_canonical hω j.1).measurableSpace ≤
      (isStoppingTime_inversePhysicalPathClock_canonical hω r).measurableSpace :=
    IsStoppingTime.measurableSpace_mono _ _ fun γ =>
      WithTop.coe_le_coe.2 ((physicalPathClockOrderIso ω γ L hω).symm.monotone hjr)
  exact (hj.mono hle le_rfl).comap_le

theorem timeChange_solves {d : ℕ} {L : ℝ} (hL : 0 < L) {ω : FieldPair d} (hω : IsRegular L ω)
    (hs : IsSmoothFieldPair ω) (i : Fin d) (lam : ℝ) (x : Vec d) {PY : Measure (Path d)}
    (hY : SolvesMartingaleProblem (reducedGenerator i ω lam) x PY) :
    SolvesMartingaleProblem (physicalGenerator i ω lam) x (PY.map (timeChangeMap hω)) := by
  obtain ⟨hprob, hstart, hf⟩ := hY
  haveI : IsProbabilityMeasure PY := hprob
  have hΦ : Measurable (timeChangeMap hω) := measurable_timeChangeMap hω
  refine ⟨inferInstance, ?_, ?_⟩
  · have hmeas : MeasurableSet {γ : Path d | γ 0 = x} :=
      (measurable_pathPosition 0) (measurableSet_singleton x)
    rw [ae_map_iff hΦ.aemeasurable hmeas]
    filter_upwards [hstart] with γ hγ
    show (inverseClockPath ω γ L hω) 0 = x
    rw [inverseClockPath_zero]
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
    have hNad := stronglyAdapted_compensatedTest (physicalGenerator i ω lam) f hf0 hLp
    have hNint : ∀ t : ℝ≥0, Integrable (compensatedTest (physicalGenerator i ω lam) f t)
        (PY.map (timeChangeMap hω)) := by
      intro t
      have hm : StronglyMeasurable (compensatedTest (physicalGenerator i ω lam) f t) :=
        (hNad t).mono ((pathFiltration d).le t)
      exact Integrable.of_bound hm.aestronglyMeasurable (2 * Cf + Cp * t)
        (Filter.Eventually.of_forall fun γ => norm_compensatedTest_le _ f hCf hCp t γ)
    refine ⟨fun t => Filter.Eventually.of_forall fun γ => ?_, hNint, ?_⟩
    · exact (hLp.comp (γ.continuous.comp continuous_real_toNNReal)).intervalIntegrable _ _
    · rw [pathFiltration_eq_canonical] at hmart ⊢
      rw [pathFiltration_eq_canonical] at hNad
      refine ⟨hNad, fun r s hrs => ?_⟩
      have hNm : ∀ t : ℝ≥0, StronglyMeasurable
          (compensatedTest (physicalGenerator i ω lam) f t) := fun t =>
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
          compensatedTest (physicalGenerator i ω lam) f t (timeChangeMap hω γ) =
            compensatedTest (reducedGenerator i ω lam) f
              (inversePhysicalPathClock ω γ L hω t) γ := fun t γ =>
        compensatedTest_physical_inverseClockPath hω hs i lam hfs γ t
      have hint' : ∀ t : ℝ≥0, Integrable (fun γ : Path d =>
          compensatedTest (reducedGenerator i ω lam) f
            (inversePhysicalPathClock ω γ L hω t) γ) PY := by
        intro t
        have h1 := (integrable_map_measure (hNm t).aestronglyMeasurable
          hΦ.aemeasurable).1 (hNint t)
        have e' : (fun γ : Path d => compensatedTest (reducedGenerator i ω lam) f
            (inversePhysicalPathClock ω γ L hω t) γ) =
            compensatedTest (physicalGenerator i ω lam) f t ∘ timeChangeMap hω :=
          funext fun γ => (e t γ).symm
        rw [e']
        exact h1
      have hbound : ∀ v : ℝ≥0, ∃ C : ℝ, ∀ t ≤ v, ∀ γ : Path d,
          ‖compensatedTest (reducedGenerator i ω lam) f t γ‖ ≤ C := by
        intro v
        refine ⟨2 * Cf + max Cr 0 * v, fun t ht γ => ?_⟩
        have h := norm_compensatedTest_le (reducedGenerator i ω lam) f (CL := max Cr 0) hCf
          (fun y => (hCr y).trans (le_max_left _ _)) t γ
        have h' : max Cr 0 * (t : ℝ) ≤ max Cr 0 * v :=
          mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.2 ht) (le_max_right _ _)
        linarith
      have hright : ∀ (γ : Path d) (v : ℝ≥0),
          ContinuousWithinAt (fun t : ℝ≥0 => compensatedTest (reducedGenerator i ω lam) f t γ)
            (Set.Ici v) v := fun γ v =>
        (continuous_compensatedTest_time _ f hf0 hLr γ).continuousWithinAt
      have hmono : ∀ γ : Path d, inversePhysicalPathClock ω γ L hω r ≤
          inversePhysicalPathClock ω γ L hω s := fun γ =>
        (physicalPathClockOrderIso ω γ L hω).symm.monotone hrs
      have hsK : ∀ γ : Path d, inversePhysicalPathClock ω γ L hω s ≤
          Real.toNNReal (Real.exp (2 * L) * s) := fun γ =>
        NNReal.le_toNNReal_of_coe_le (inversePhysicalPathClock_bounds ω γ L hω s).2
      have hB' := measurable_timeChangeMap_stopped hω r hB
      have key := setIntegral_stoppedValue_eq (μ := PY) hmart hbound hright
        (isStoppingTime_inversePhysicalPathClock_canonical hω r)
        (isStoppingTime_inversePhysicalPathClock_canonical hω s) hmono
        (fun γ => (hmono γ).trans (hsK γ)) hsK (hint' r) (hint' s) hB'
      have lhs : ∫ x in timeChangeMap hω ⁻¹' B,
          compensatedTest (physicalGenerator i ω lam) f r (timeChangeMap hω x) ∂PY =
          ∫ x in timeChangeMap hω ⁻¹' B, compensatedTest (reducedGenerator i ω lam) f
            (inversePhysicalPathClock ω x L hω r) x ∂PY :=
        setIntegral_congr_fun (hΦ hBm) fun γ _ => e r γ
      have rhs : ∫ x in timeChangeMap hω ⁻¹' B,
          compensatedTest (physicalGenerator i ω lam) f s (timeChangeMap hω x) ∂PY =
          ∫ x in timeChangeMap hω ⁻¹' B, compensatedTest (reducedGenerator i ω lam) f
            (inversePhysicalPathClock ω x L hω s) x ∂PY :=
        setIntegral_congr_fun (hΦ hBm) fun γ _ => e s γ
      rw [lhs, rhs]
      exact key.symm

end EinsteinFull
