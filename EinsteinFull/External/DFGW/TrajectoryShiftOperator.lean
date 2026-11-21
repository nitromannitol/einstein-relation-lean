import EinsteinFull.External.DFGW.TrajectoryProjectionMean

/-! # Shift operators on trajectory observables

The stationary shift induces an isometric operator on trajectory `L²` which fixes constants.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The `L²` operator induced by a trajectory time shift. -/
noncomputable def trajectoryShiftOperator (hP : Draft.IsDFGWTrajectoryProcess P μ T) (t : ℝ≥0) :
    Lp ℝ 2 P →L[ℝ] Lp ℝ 2 P :=
  (Lp.compMeasurePreservingₗᵢ (E := ℝ) (p := 2) ℝ _ ⟨measurable_shift _, hP.stationary t⟩).toContinuousLinearMap

omit [BorelSpace S] in
/-- The trajectory shift operator is a contraction. -/
theorem norm_trajectoryShiftOperator_le_one (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (t : ℝ≥0) : ‖trajectoryShiftOperator hP t‖ ≤ 1 :=
  (Lp.compMeasurePreservingₗᵢ (E := ℝ) (p := 2) ℝ _ ⟨measurable_shift _, hP.stationary t⟩).norm_toContinuousLinearMap_le

omit [BorelSpace S] in
/-- Every constant `L²` observable is fixed by the trajectory shift. -/
theorem trajectoryShiftOperator_const (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hPfin : P Set.univ ≠ ⊤) (t : ℝ≥0) (c : ℝ) :
    trajectoryShiftOperator hP t (indicatorConstLp 2 MeasurableSet.univ hPfin c) =
      indicatorConstLp 2 MeasurableSet.univ hPfin c := by
  let hshift : MeasurePreserving (Draft.dfgwShift (S := S) t) P P :=
    ⟨measurable_shift _, hP.stationary _⟩
  let k : Lp ℝ 2 P := indicatorConstLp 2 MeasurableSet.univ hPfin c
  have hk : k =ᵐ[P] fun _ => c := by
    filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := MeasurableSet.univ)
      (hμs := hPfin) (c := c)] with η hη
    simpa only [k, Set.indicator_univ] using hη
  have hs := hshift.quasiMeasurePreserving.ae hk
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving k hshift, hs, hk] with η ha hb hc
  simp only [Function.comp_apply] at ha hb
  change Lp.compMeasurePreserving _ hshift k η = k η
  rw [ha, hb, hc]

end EinsteinFull.External.DFGW
