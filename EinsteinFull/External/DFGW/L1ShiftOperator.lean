import EinsteinFull.External.DFGW.TrajectoryShiftOperator
import EinsteinFull.External.DFGW.LpTwoToOne
import Mathlib.MeasureTheory.Integral.Bochner.L1

/-! # Shift and mean operators on `L¹`

The `L¹` shift operator commutes with the natural inclusion of `L²`, and the mean operator
sends an observable to the corresponding constant.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The stationary trajectory shift acting on `L¹`. -/
noncomputable def trajectoryShiftOperatorL1 (hP : Draft.IsDFGWTrajectoryProcess P μ T) (t : ℝ≥0) :
    Lp ℝ 1 P →L[ℝ] Lp ℝ 1 P :=
  (Lp.compMeasurePreservingₗᵢ (E := ℝ) (p := 1) ℝ _
    ⟨measurable_shift _, hP.stationary t⟩).toContinuousLinearMap

omit [BorelSpace S] in
/-- The `L¹` trajectory shift is a contraction. -/
theorem norm_trajectoryShiftOperatorL1_le_one (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (t : ℝ≥0) : ‖trajectoryShiftOperatorL1 hP t‖ ≤ 1 :=
  (Lp.compMeasurePreservingₗᵢ (E := ℝ) (p := 1) ℝ _
    ⟨measurable_shift _, hP.stationary t⟩).norm_toContinuousLinearMap_le

omit [BorelSpace S] in
/-- `L²` inclusion intertwines the `L²` and `L¹` trajectory shifts. -/
theorem lpTwoToOne_shift (hP : Draft.IsDFGWTrajectoryProcess P μ T) (t : ℝ≥0)
    (f : Lp ℝ 2 P) :
    letI : IsProbabilityMeasure P := hP.probability
    lpTwoToOne P (trajectoryShiftOperator hP t f) =
      trajectoryShiftOperatorL1 hP t (lpTwoToOne P f) := by
  let : IsProbabilityMeasure P := hP.probability
  let hshift : MeasurePreserving (Draft.dfgwShift (S := S) t) P P :=
    ⟨measurable_shift _, hP.stationary _⟩
  have hJ := hshift.quasiMeasurePreserving.ae (lpTwoToOne_ae P f)
  apply Lp.ext
  filter_upwards [lpTwoToOne_ae P (trajectoryShiftOperator hP t f),
    Lp.coeFn_compMeasurePreserving f hshift,
    Lp.coeFn_compMeasurePreserving (lpTwoToOne P f) hshift, hJ] with η ha hb hc hd
  change lpTwoToOne P (trajectoryShiftOperator hP t f) η =
    Lp.compMeasurePreserving _ hshift (lpTwoToOne P f) η
  change trajectoryShiftOperator hP t f η = f (Draft.dfgwShift t η) at hb
  rw [ha, hb, hc]
  exact hd.symm

/-- The projection of an integrable trajectory observable onto its mean. -/
noncomputable def trajectoryMeanOperator (_hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hPfin : P Set.univ ≠ ⊤) : Lp ℝ 1 P →L[ℝ] Lp ℝ 1 P :=
  (ContinuousLinearMap.toSpanSingleton ℝ (indicatorConstLp 1 MeasurableSet.univ hPfin (1 : ℝ))).comp
    (L1.integralCLM (α := C(ℝ, S)) (E := ℝ) (μ := P))

omit [BorelSpace S] in
/-- The mean projection agrees with the mean of an included `L²` observable. -/
theorem trajectoryMeanOperator_lpTwoToOne (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hPfin : P Set.univ ≠ ⊤) (f : Lp ℝ 2 P) :
    letI : IsProbabilityMeasure P := hP.probability
    trajectoryMeanOperator hP hPfin (lpTwoToOne P f) =
      lpTwoToOne P (indicatorConstLp 2 MeasurableSet.univ hPfin (∫ η, f η ∂P)) := by
  let : IsProbabilityMeasure P := hP.probability
  have hint : L1.integralCLM (lpTwoToOne P f) = ∫ η, f η ∂P := by
    rw [← L1.integral_eq, L1.integral_eq_integral]
    exact integral_congr_ae (lpTwoToOne_ae P f)
  have hone := indicatorConstLp_coeFn (p := 1) (hs := MeasurableSet.univ)
    (hμs := hPfin) (c := (1 : ℝ))
  have htwo := indicatorConstLp_coeFn (p := 2) (hs := MeasurableSet.univ)
    (hμs := hPfin) (c := ∫ η, f η ∂P)
  have hJ := lpTwoToOne_ae P (indicatorConstLp 2 MeasurableSet.univ hPfin (∫ η, f η ∂P))
  apply Lp.ext
  filter_upwards [hone, htwo, hJ,
    Lp.coeFn_smul (∫ η, f η ∂P) (indicatorConstLp 1 MeasurableSet.univ hPfin (1 : ℝ))] with η h1 h2 h3 h4
  change (L1.integralCLM (lpTwoToOne P f) •
      indicatorConstLp 1 MeasurableSet.univ hPfin (1 : ℝ)) η = _
  rw [hint, h4]
  simp only [Pi.smul_apply]
  rw [h1, h3, h2]
  simp only [Set.indicator_univ, smul_eq_mul, mul_one]

end EinsteinFull.External.DFGW
