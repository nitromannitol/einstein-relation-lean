import EinsteinRelation.Environment.FieldMeasurability

/-!
# Rescaling continuous coefficient fields

Source: `paper/main.tex:699-708`. Spatial dilation and scalar matrix
multiplication act measurably on the actual continuous-field carrier.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation

/-- Simultaneously rescale space and the matrix values of a continuous field. -/
def rescaleCoefficientField {d : ℕ} (c r : ℝ) (a : CoefficientField d) :
    CoefficientField d :=
  ⟨fun x => c • a (r • x),
    continuous_const.smul (a.continuous.comp (continuous_const.smul continuous_id))⟩

/-- Fixed rescaling is measurable for the compact-open Borel field carrier. -/
theorem measurable_rescaleCoefficientField (d : ℕ) (c r : ℝ) :
    Measurable (rescaleCoefficientField (d := d) c r) := by
  letI : PolishSpace (Mat d) := inferInstanceAs (PolishSpace (Fin d → Fin d → ℝ))
  letI : PolishSpace (CoefficientField d) := Localization.coefficientField_polish d
  letI : MeasurableSpace (CoefficientField d) := borel (CoefficientField d)
  letI : BorelSpace (CoefficientField d) := ⟨rfl⟩
  apply measurable_continuousMap_of_evaluations
  intro x
  exact measurable_const.smul (continuous_eval_const (r • x)).measurable

/-- Opposite nonzero rescalings cancel pointwise. -/
theorem rescaleCoefficientField_inv {d : ℕ} (c r : ℝ) (hc : c ≠ 0) (hr : r ≠ 0)
    (a : CoefficientField d) :
    rescaleCoefficientField c⁻¹ r⁻¹ (rescaleCoefficientField c r a) = a := by
  ext x i j
  simp [rescaleCoefficientField, smul_smul, inv_mul_cancel₀ hc, mul_inv_cancel₀ hr]

end EinsteinRelation
