import EinsteinFull.Regeneration.CoordinateSlabStopping

/-!
# Successive capped slab stopping times

The successive capped slab clock depends on the path only up to its current
time, so each of its entries is a canonical stopping time.
-/

open MeasureTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- A capped exit is the minimum of the uncapped exit and the time cap. -/
theorem coe_cappedCoordinateSlabExit {d : ℕ} (γ : Path d) (i : Fin d) (r : ℝ) (g : ℝ≥0) :
    (cappedCoordinateSlabExit γ i r g : ℝ≥0∞) =
      min (coordinateSlabExit γ i r) (g : ℝ≥0∞) := by
  by_cases hfin : coordinateSlabExit γ i r = ⊤
  · simp [cappedCoordinateSlabExit, hfin]
  · simp [cappedCoordinateSlabExit, hfin, ENNReal.coe_min, ENNReal.coe_toNNReal hfin]

/-- Capped-exit sublevels depend only on the path before their threshold. -/
theorem cappedCoordinateSlabExit_le_iff_of_prefix {d : ℕ} (γ η : Path d)
    (i : Fin d) (r : ℝ) (g T : ℝ≥0) (hprefix : ∀ t ≤ T, γ t = η t) :
    cappedCoordinateSlabExit γ i r g ≤ T ↔ cappedCoordinateSlabExit η i r g ≤ T := by
  rw [← ENNReal.coe_le_coe, ← ENNReal.coe_le_coe,
    coe_cappedCoordinateSlabExit, coe_cappedCoordinateSlabExit]
  simp only [min_le_iff]
  exact or_congr (coordinateSlabExit_le_iff_of_prefix γ η i r T hprefix) Iff.rfl

/-- An exit occurring within a common prefix has the same capped time for both paths. -/
theorem cappedCoordinateSlabExit_eq_of_prefix {d : ℕ} (γ η : Path d)
    (i : Fin d) (r : ℝ) (g T : ℝ≥0) (hprefix : ∀ t ≤ T, γ t = η t)
    (hγ : cappedCoordinateSlabExit γ i r g ≤ T) :
    cappedCoordinateSlabExit γ i r g = cappedCoordinateSlabExit η i r g := by
  have hηle : cappedCoordinateSlabExit η i r g ≤ cappedCoordinateSlabExit γ i r g :=
    (cappedCoordinateSlabExit_le_iff_of_prefix γ η i r g _
      (fun t ht => hprefix t (ht.trans hγ))).mp le_rfl
  have hγle : cappedCoordinateSlabExit γ i r g ≤ cappedCoordinateSlabExit η i r g :=
    (cappedCoordinateSlabExit_le_iff_of_prefix γ η i r g _
      (fun t ht => hprefix t (ht.trans (hηle.trans hγ)))).mpr le_rfl
  exact le_antisymm hγle hηle

/-- A successive exit occurring in a common prefix is determined by that prefix. -/
theorem cappedSlabExitTime_eq_of_prefix {d : ℕ} (γ η : Path d)
    (i : Fin d) (r : ℝ) (g T : ℝ≥0) (hprefix : ∀ t ≤ T, γ t = η t)
    (n : ℕ) (hγ : cappedSlabExitTime γ i r g n ≤ T) :
    cappedSlabExitTime γ i r g n = cappedSlabExitTime η i r g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hprev : cappedSlabExitTime γ i r g n ≤ T :=
      (monotone_cappedSlabExitTime γ i r g (Nat.le_succ n)).trans hγ
    have heq := ih hprev
    have hstep : cappedCoordinateSlabExit
        (pathTimeShift γ (cappedSlabExitTime γ i r g n)) i r g ≤
        T - cappedSlabExitTime γ i r g n := by
      apply le_tsub_of_add_le_left
      simpa only [cappedSlabExitTime_succ, add_comm] using hγ
    have hshift (t : ℝ≥0) (ht : t ≤ T - cappedSlabExitTime γ i r g n) :
        pathTimeShift γ (cappedSlabExitTime γ i r g n) t =
          pathTimeShift η (cappedSlabExitTime γ i r g n) t := by
      apply hprefix
      exact add_le_of_le_tsub_left_of_le hprev ht
    have hstep_eq := cappedCoordinateSlabExit_eq_of_prefix
      (pathTimeShift γ (cappedSlabExitTime γ i r g n))
      (pathTimeShift η (cappedSlabExitTime γ i r g n)) i r g _ hshift hstep
    rw [cappedSlabExitTime_succ, cappedSlabExitTime_succ, ← heq, hstep_eq]

/-- Every successive capped slab exit is a canonical stopping time. -/
theorem isStoppingTime_cappedSlabExitTime {d : ℕ} (i : Fin d) (r : ℝ) (g : ℝ≥0) (n : ℕ) :
    IsStoppingTime (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d))
      (fun γ : Path d => (cappedSlabExitTime γ i r g n : ℝ≥0∞)) := by
  intro T
  have heq : {γ : Path d | (cappedSlabExitTime γ i r g n : ℝ≥0∞) ≤ T} =
      (MarkovProcess.ContinuousPath.stoppedPath T) ⁻¹'
        {γ : Path d | (cappedSlabExitTime γ i r g n : ℝ≥0∞) ≤ T} := by
    ext γ
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, ENNReal.coe_le_coe]
    constructor
    · intro hγ
      rw [← cappedSlabExitTime_eq_of_prefix γ (MarkovProcess.ContinuousPath.stoppedPath T γ)
        i r g T (fun t ht => (MarkovProcess.ContinuousPath.stoppedPath_apply_of_le T γ t ht).symm)
        n hγ]
      exact hγ
    · intro hη
      rw [← cappedSlabExitTime_eq_of_prefix (MarkovProcess.ContinuousPath.stoppedPath T γ) γ
        i r g T (fun t ht => MarkovProcess.ContinuousPath.stoppedPath_apply_of_le T γ t ht)
        n hη]
      exact hη
  change @MeasurableSet (Path d)
    (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d) T)
    {γ : Path d | (cappedSlabExitTime γ i r g n : ℝ≥0∞) ≤ T}
  rw [heq]
  exact measurable_stoppedPath_canonicalHistory T
    (((measurable_cappedSlabExitTime i r g n).coe_nnreal_ennreal) measurableSet_Iic)

end EinsteinFull.Regeneration
