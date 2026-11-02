import EinsteinRelation.Environment.AKMContinuousFieldMeasurability
import Mathlib.MeasureTheory.Function.FactorsThrough

/-!
# A measurable continuous reconstruction on the AKM carrier

Source: `paper/main.tex:693-698` and AKM (0.11). Smooth observations
recover every continuous coefficient exactly. Extending that measurable
map gives a continuous field on the whole raw carrier. No continuity
property is asserted of a general raw coefficient.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation.Environment.AKMTestIntegralSupport

/-- A measurable reconstruction agrees pointwise with every continuous
coefficient, without requiring a measurable continuous-coefficient subset. -/
theorem exists_measurable_continuous_reconstruction {d : ℕ} {K : ℝ} :
    ∃ R : Coefficient d K → CoefficientField d, Measurable R ∧
      ∀ (a : Coefficient d K) (ha : Continuous a.field), R a = ⟨a.field, ha⟩ := by
  letI : PolishSpace (Mat d) := inferInstanceAs (PolishSpace (Fin d → Fin d → ℝ))
  letI : PolishSpace (CoefficientField d) := Localization.coefficientField_polish d
  letI : MeasurableSpace (CoefficientField d) := borel (CoefficientField d)
  letI : BorelSpace (CoefficientField d) := ⟨rfl⟩
  obtain ⟨R, hR, heq⟩ :=
    (measurable_continuous_field_of_akm_observations (d := d) (K := K)).exists_eq_measurable_comp
  refine ⟨R, hR, fun a ha => ?_⟩
  exact (congrFun heq (⟨a, ha⟩ : {a : Coefficient d K // Continuous a.field})).symm

end EinsteinRelation.Environment.AKMTestIntegralSupport
