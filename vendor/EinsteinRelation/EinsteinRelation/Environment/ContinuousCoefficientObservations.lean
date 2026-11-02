import EinsteinRelation.Environment.AKMTestIntegralSupport
import EinsteinRelation.Environment.FieldMeasurability
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

open MeasureTheory Filter
open scoped Topology Convolution

noncomputable section

namespace EinsteinRelation.Environment.AKMTestIntegralSupport

/-! ## Delta sequence for point evaluation

We construct a sequence of `SmoothCompactTest` functions that approximate the Dirac
delta at a point `x`. These are used to show that point evaluations are limits of
test integrals, and hence measurable on the continuous-coefficient subtype.
-/

private def observationBump (d n : ℕ) : ContDiffBump (0 : Vec d) where
  rIn := 1 / ((n : ℝ) + 1) / 2
  rOut := 1 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith

def coefficientEvaluationTest {d : ℕ} (x : Vec d) (n : ℕ) : SmoothCompactTest d :=
  ⟨fun y => (observationBump d n).normed volume (x - y),
    (observationBump d n).contDiff_normed.comp (contDiff_const.sub contDiff_id),
    (observationBump d n).hasCompactSupport_normed.comp_homeomorph (Homeomorph.subLeft x)⟩

/-- For a coefficient with continuous field, test integrals against the delta sequence
converge to the point evaluation. Source: `paper/main.tex:693-698` and AKM (0.11). -/
theorem tendsto_testIntegral_point_evaluation {d : ℕ} {K : ℝ}
    (a : Coefficient d K) (ha : Continuous a.field) (x : Vec d) (i j : Fin d) :
    Tendsto (fun n => testIntegral a (coefficientEvaluationTest x n) i j)
      atTop (𝓝 (a.field x i j)) := by
  have hc : Continuous (fun y => a.field y i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp ha)
  have h := ContDiffBump.convolution_tendsto_right_of_continuous
    (μ := (volume : Measure (Vec d))) (φ := observationBump d)
    tendsto_one_div_add_atTop_nhds_zero_nat hc x
  simpa only [convolution_eq_swap, ContinuousLinearMap.lsmul_apply, smul_eq_mul,
    testIntegral, coefficientEvaluationTest] using h

/-- For a fixed point `x` and matrix entry `(i, j)`, the map
`a ↦ a.1.field x i j` is measurable on the subtype of coefficients with continuous field.

The proof uses the delta sequence `coefficientEvaluationTest` and the fact that
pointwise limits of measurable functions are measurable (`measurable_of_tendsto_metrizable`). -/
lemma measurable_coefficientField_eval {d : ℕ} {K : ℝ} (x : Vec d) (i j : Fin d) :
    Measurable (fun (a : {a : Coefficient d K // Continuous a.field}) =>
      a.1.field x i j) := by
  apply measurable_of_tendsto_metrizable
    (fun n => (measurable_testIntegral (coefficientEvaluationTest x n) i j).comp measurable_subtype_coe)
  refine tendsto_pi_nhds.mpr fun a => ?_
  exact tendsto_testIntegral_point_evaluation a.1 a.2 x i j

/-- On continuous coefficients, the test-integral sigma algebra observes
the actual compact-open continuous field. Approximate point evaluations
by smooth compact kernels; source `paper/main.tex:693-698` and AKM (0.11). -/
theorem measurable_continuous_coefficientField {d : ℕ} {K : ℝ} :
    Measurable (fun a : {a : Coefficient d K // Continuous a.field} =>
      (⟨a.1.field, a.2⟩ : CoefficientField d)) := by
  letI : PolishSpace (Mat d) := inferInstanceAs (PolishSpace (Fin d → Fin d → ℝ))
  letI : PolishSpace (CoefficientField d) := Localization.coefficientField_polish d
  letI : MeasurableSpace (CoefficientField d) := borel (CoefficientField d)
  letI : BorelSpace (CoefficientField d) := ⟨rfl⟩
  refine measurable_continuousMap_of_evaluations
    (fun a : {a : Coefficient d K // Continuous a.field} => (⟨a.1.field, a.2⟩ : CoefficientField d)) ?_
  intro x
  change @Measurable _ (Fin d → Fin d → ℝ) _ (borel _) _
  rw [← (Pi.borelSpace (X := fun _ : Fin d => Fin d → ℝ)).measurable_eq]
  refine measurable_pi_iff.mpr fun i => ?_
  refine measurable_pi_iff.mpr fun j => ?_
  exact measurable_coefficientField_eval x i j

end EinsteinRelation.Environment.AKMTestIntegralSupport
