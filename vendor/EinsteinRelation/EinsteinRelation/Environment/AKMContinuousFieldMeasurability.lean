import EinsteinRelation.Environment.ContinuousCoefficientObservations
import EinsteinRelation.Environment.FieldMeasurability
import EinsteinRelation.Environment.AKMTestIntegralSupport
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/-!
# Recovering continuous fields from AKM observations

Source: `paper/main.tex:693-698` and AKM (0.11). On the continuous
subtype, smooth local averages recover point evaluations and hence the
compact-open Borel field. Point evaluation on the full raw carrier is
not needed.
-/

open MeasureTheory Filter
open scoped Topology Convolution
noncomputable section
namespace EinsteinRelation.Environment.AKMTestIntegralSupport

private def observationBump (d n : ℕ) : ContDiffBump (0 : Vec d) where
  rIn := 1 / ((n : ℝ) + 1) / 2
  rOut := 1 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith

/-- The AKM observation sigma algebra on continuous coefficients observes
its genuine compact-open continuous field. -/
theorem measurable_continuous_field_of_akm_observations {d : ℕ} {K : ℝ} :
    Measurable (fun a : {a : Coefficient d K // Continuous a.field} =>
      (⟨a.1.field, a.2⟩ : CoefficientField d)) := by
  letI : PolishSpace (Mat d) := inferInstanceAs (PolishSpace (Fin d → Fin d → ℝ))
  letI : PolishSpace (CoefficientField d) := Localization.coefficientField_polish d
  letI : MeasurableSpace (CoefficientField d) := borel (CoefficientField d)
  letI : BorelSpace (CoefficientField d) := ⟨rfl⟩
  apply measurable_continuousMap_of_evaluations
  intro x
  change @Measurable _ (Fin d → Fin d → ℝ) _ (borel _) _
  rw [← (Pi.borelSpace (X := fun _ : Fin d => Fin d → ℝ)).measurable_eq]
  apply measurable_pi_iff.mpr
  intro i
  apply measurable_pi_iff.mpr
  intro j
  apply measurable_of_tendsto_metrizable
    (fun n => (measurable_testIntegral (coefficientEvaluationTest x n) i j).comp measurable_subtype_coe)
  exact tendsto_pi_nhds.mpr fun a => tendsto_testIntegral_point_evaluation a.1 a.2 x i j

end EinsteinRelation.Environment.AKMTestIntegralSupport
