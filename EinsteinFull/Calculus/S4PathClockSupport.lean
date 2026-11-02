import EinsteinFull.Calculus.S4SmoothGeneratorSupport
import EinsteinRelation.Diffusion.ClockInverseSupport
import EinsteinRelation.Diffusion.JointClockPathMapSupport
import MarkovProcess.Trajectory.ClampedCoordinate
import MarkovProcess.Path.OptionalStopping
import MarkovProcess.Path.StoppedValueMeasurability

/-!
# Adaptedness and stopping-time facts on path space for the time change

* `pathFiltration d` is the canonical filtration of the `MarkovProcess` library;
* `γ ↦ ∫₀ᵗ g (γ u) du` is measurable for the time-`t` σ-algebra when `g` is continuous;
  hence `compensatedTest L f` is adapted whenever `L f` is continuous;
* the inverse clock `γ ↦ A_γ⁻¹ (s)` is a stopping time of the canonical filtration.
-/

open MeasureTheory
open scoped NNReal

namespace EinsteinFull
open EinsteinRelation

theorem pathFiltration_eq_canonical (d : ℕ) :
    pathFiltration d = MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d) := by
  refine Filtration.ext (funext fun t => ?_)
  refine le_antisymm ?_ ?_
  · exact iSup₂_le fun j hj => le_iSup_of_le (⟨j, hj⟩ : Set.Iic t) le_rfl
  · exact iSup_le fun s => le_iSup₂_of_le s.1 s.2 le_rfl

theorem stronglyMeasurable_integral_prod' {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (μ : Measure ℝ) [SFinite μ] {phi : ℝ × Ω → ℝ}
    (hphi : StronglyMeasurable[(borel ℝ).prod mΩ] phi) :
    StronglyMeasurable[mΩ] fun ω : Ω => ∫ s, phi (s, ω) ∂μ :=
  hphi.integral_prod_left'

theorem stronglyMeasurable_pathIntegral {d : ℕ} (g : Vec d → ℝ) (hg : Continuous g) (t : ℝ≥0) :
    StronglyMeasurable[MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d) t]
      (fun γ : Path d => ∫ s in (0 : ℝ)..t, g (γ s.toNNReal)) := by
  have hcl := MarkovProcess.ContinuousPath.measurable_clampedCoordinate (alpha := Vec d) t
  have hphi : StronglyMeasurable[(borel ℝ).prod
      (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d) t)]
      (fun p : ℝ × Path d => g (p.2 (min (Real.toNNReal p.1) t))) :=
    hg.comp_stronglyMeasurable hcl.stronglyMeasurable
  have hprod : StronglyMeasurable[MarkovProcess.ContinuousPath.canonicalFiltration
      (alpha := Vec d) t] (fun γ : Path d =>
        ∫ s, g (γ (min (Real.toNNReal s) t)) ∂(volume.restrict (Set.Ioc (0 : ℝ) t))) :=
    stronglyMeasurable_integral_prod' (volume.restrict (Set.Ioc (0 : ℝ) t)) hphi
  have hfun : (fun γ : Path d => ∫ s in (0 : ℝ)..t, g (γ s.toNNReal)) =
      fun γ : Path d => ∫ s, g (γ (min (Real.toNNReal s) t))
        ∂(volume.restrict (Set.Ioc (0 : ℝ) t)) := by
    funext γ
    rw [intervalIntegral.integral_of_le t.coe_nonneg]
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    rw [min_eq_left (Real.toNNReal_le_iff_le_coe.mpr hs.2)]
  rw [hfun]
  exact hprod

theorem stronglyAdapted_compensatedTest {d : ℕ} (L : (Vec d → ℝ) → Vec d → ℝ) (f : Vec d → ℝ)
    (hf : Continuous f) (hLf : Continuous (L f)) :
    StronglyAdapted (pathFiltration d) (compensatedTest L f) := by
  intro t
  rw [pathFiltration_eq_canonical]
  have h1 : StronglyMeasurable[MarkovProcess.ContinuousPath.canonicalFiltration
      (alpha := Vec d) t] (fun γ : Path d => f (γ t)) :=
    hf.comp_stronglyMeasurable
      (MarkovProcess.ContinuousPath.measurable_coordinateProcess_canonicalFiltration
        (alpha := Vec d) t).stronglyMeasurable
  have h0 : StronglyMeasurable[MarkovProcess.ContinuousPath.canonicalFiltration
      (alpha := Vec d) t] (fun γ : Path d => f (γ 0)) :=
    hf.comp_stronglyMeasurable
      (((MarkovProcess.ContinuousPath.measurable_coordinateProcess_canonicalFiltration
        (alpha := Vec d) 0).mono
        ((MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d)).mono zero_le)
        le_rfl).stronglyMeasurable)
  have hint := stronglyMeasurable_pathIntegral (L f) hLf t
  exact (h1.sub h0).sub hint

theorem isStoppingTime_inversePhysicalPathClock {d : ℕ} {L : ℝ} {ω : FieldPair d}
    (hω : IsRegular L ω) (s : ℝ≥0) :
    IsStoppingTime (pathFiltration d) (fun γ : Path d =>
      ((Clock.InverseMeaningV3.inversePhysicalPathClock ω γ L hω s : ℝ≥0) :
        WithTop ℝ≥0)) := by
  intro t
  have hset : {γ : Path d | ((Clock.InverseMeaningV3.inversePhysicalPathClock ω γ L hω s : ℝ≥0) :
      WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)} =
      {γ : Path d | (s : ℝ) ≤ Clock.pathClock (clockDensity ω) γ t} := by
    ext γ
    simp only [Set.mem_setOf_eq, WithTop.coe_le_coe]
    have h := (Clock.InverseMeaningV3.physicalPathClockOrderIso ω γ L hω).symm_apply_le
      (x := t) (y := s)
    rw [Clock.InverseMeaningV3.physicalPathClockOrderIso_apply] at h
    exact h.trans NNReal.coe_le_coe.symm
  rw [hset, pathFiltration_eq_canonical]
  have hmeas := (stronglyMeasurable_pathIntegral (clockDensity ω) (reduce ω).2.continuous t).measurable
  exact measurableSet_le measurable_const hmeas

end EinsteinFull
