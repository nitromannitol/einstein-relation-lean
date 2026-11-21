import EinsteinFull.Regeneration.SuccessiveSlabStopping
import EinsteinFull.Regeneration.ForwardHittingNaturalFiltration
import MarkovProcess.Path.StoppedValueMeasurability

/-!
# Stopped filtrations for capped slab increments

The filtration at successive capped exits contains the natural filtration of
the corresponding coordinate increments.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- Canonical histories at the ends of successive capped slab steps. -/
noncomputable def cappedSlabStoppedFiltration {d : ℕ} (i : Fin d) (r : ℝ) (g : ℝ≥0) :
    Filtration ℕ (borel (Path d)) where
  seq n := (isStoppingTime_cappedSlabExitTime i r g (n + 1)).measurableSpace
  mono' n m hnm := IsStoppingTime.measurableSpace_mono
    (isStoppingTime_cappedSlabExitTime i r g (n + 1))
    (isStoppingTime_cappedSlabExitTime i r g (m + 1))
    (fun γ => ENNReal.coe_le_coe.mpr
      (monotone_cappedSlabExitTime γ i r g (Nat.add_le_add_right hnm 1)))
  le' n := (isStoppingTime_cappedSlabExitTime i r g (n + 1)).measurableSpace_le

/-- The actual capped increments are measurable at the ends of their steps. -/
theorem stronglyAdapted_cappedSlabIncrement_stopped {d : ℕ} (i : Fin d) (r : ℝ) (g : ℝ≥0) :
    StronglyAdapted (cappedSlabStoppedFiltration i r g)
      (fun (n : ℕ) (γ : Path d) => cappedSlabIncrement γ i r g n) := by
  intro n
  have hstate (k : ℕ) : Measurable[
      (isStoppingTime_cappedSlabExitTime i r g k).measurableSpace]
      (fun γ : Path d => γ (cappedSlabExitTime γ i r g k) i) :=
    (measurable_pi_apply i).comp (MarkovProcess.ContinuousPath.measurable_eval_stoppingTime
      (fun γ : Path d => cappedSlabExitTime γ i r g k)
      (isStoppingTime_cappedSlabExitTime i r g k))
  have hle : (isStoppingTime_cappedSlabExitTime i r g n).measurableSpace ≤
      (isStoppingTime_cappedSlabExitTime i r g (n + 1)).measurableSpace :=
    IsStoppingTime.measurableSpace_mono (isStoppingTime_cappedSlabExitTime i r g n)
      (isStoppingTime_cappedSlabExitTime i r g (n + 1))
      (fun γ => ENNReal.coe_le_coe.mpr
        (monotone_cappedSlabExitTime γ i r g (Nat.le_succ n)))
  exact (((hstate (n + 1)).sub ((hstate n).mono hle le_rfl)).div_const r).stronglyMeasurable

/-- The increment history is contained in the canonical history at the end of each step. -/
theorem cappedSlabNaturalFiltration_le_stopped {d : ℕ} (i : Fin d) (r : ℝ) (g : ℝ≥0) :
    cappedSlabNaturalFiltration (id : Path d → Path d) measurable_id i r g ≤
      cappedSlabStoppedFiltration i r g := by
  intro n
  change (⨆ j ≤ n, MeasurableSpace.comap
    (fun γ : Path d => cappedSlabIncrement γ i r g j) inferInstance) ≤
      cappedSlabStoppedFiltration i r g n
  refine iSup₂_le fun j hj => ?_
  exact ((stronglyAdapted_cappedSlabIncrement_stopped i r g j).measurable.mono
    ((cappedSlabStoppedFiltration i r g).mono hj) le_rfl).comap_le

end EinsteinFull.Regeneration
