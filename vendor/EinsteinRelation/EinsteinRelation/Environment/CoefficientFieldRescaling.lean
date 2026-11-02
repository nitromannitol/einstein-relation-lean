import EinsteinRelation.Environment.FieldMeasurability

/-!
# Rescaling continuous coefficient fields

Source: `paper/main.tex:693-702`. Spatial dilation and scalar matrix
multiplication act measurably on the actual continuous-field carrier.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation

/-- Simultaneously rescale space and the matrix values of a continuous field. -/
def rescaleCoefficientField {d : ℕ} (c r : ℝ) (a : CoefficientField d) :
    CoefficientField d :=
  ⟨fun x => c • a (r • x),
    Continuous.fun_smul continuous_const
      (a.continuous.comp (Continuous.fun_smul continuous_const continuous_id))⟩

/-- Fixed rescaling is measurable for the compact-open Borel field carrier. -/
theorem measurable_rescaleCoefficientField (d : ℕ) (c r : ℝ) :
    Measurable (rescaleCoefficientField (d := d) c r) := by
  letI : PolishSpace (Mat d) := inferInstanceAs (PolishSpace (Fin d → Fin d → ℝ))
  letI : PolishSpace (CoefficientField d) := Localization.coefficientField_polish d
  letI : MeasurableSpace (CoefficientField d) := borel (CoefficientField d)
  letI : BorelSpace (CoefficientField d) := ⟨rfl⟩
  apply measurable_continuousMap_of_evaluations
  intro x
  have hev : Continuous (fun a : CoefficientField d => a (r • x)) :=
    continuous_eval_const (r • x)
  exact hev.measurable.const_smul c

/-- Opposite nonzero rescalings cancel pointwise. -/
theorem rescaleCoefficientField_inv {d : ℕ} (c r : ℝ) (hc : c ≠ 0) (hr : r ≠ 0)
    (a : CoefficientField d) :
    rescaleCoefficientField c⁻¹ r⁻¹ (rescaleCoefficientField c r a) = a := by
  ext x i j
  simp [rescaleCoefficientField, smul_smul, inv_mul_cancel₀ hc, mul_inv_cancel₀ hr]

end EinsteinRelation
