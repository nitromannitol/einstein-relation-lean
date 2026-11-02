import EinsteinRelation.Environment.FieldMeasurability
import EinsteinRelation.Sharpness.Fields
import Mathlib.Analysis.Calculus.FDeriv.Measurable
open MeasureTheory
namespace EinsteinRelation.Sharpness
/-- Actual coordinate differentiation evaluated on the compact-open field carrier
is Borel measurable. Source main.tex1218–1231, for the physical density map.
This uses joint continuous evaluation and Mathlib's parameter derivative theorem;
it does not assume differentiability of arbitrary continuous input fields. -/
theorem measurable_continuousMap_coordinateDerivative (d : ℕ) (i : Fin d) :
    letI : MeasurableSpace C(Vec d, ℝ) := borel C(Vec d, ℝ)
    Measurable (fun p : C(Vec d, ℝ) × Vec d => coordinateDerivative i (p.1 : Vec d → ℝ) p.2) := by
  letI : MeasurableSpace C(Vec d, ℝ) := borel C(Vec d, ℝ)
  letI : BorelSpace C(Vec d, ℝ) := ⟨rfl⟩
  exact measurable_fderiv_apply_const_with_param ℝ
    (f := fun H : C(Vec d, ℝ) => (H : Vec d → ℝ)) continuous_eval (unitVector i)

/-- A measurable actual continuous random field has measurable evaluated coordinate derivatives.
No extra smoothness premise is needed for the total Fréchet derivative operation. -/
theorem measurable_coordinateDerivative_of_measurable_continuousMap
    {Ω : Type} [MeasurableSpace Ω] {d : ℕ} (F : Ω → C(Vec d, ℝ))
    (hF : @Measurable Ω C(Vec d, ℝ) inferInstance (borel C(Vec d, ℝ)) F)
    (i : Fin d) (x : Vec d) :
    Measurable (fun ω => coordinateDerivative i (F ω : Vec d → ℝ) x) := by
  letI : MeasurableSpace C(Vec d, ℝ) := borel C(Vec d, ℝ)
  exact (measurable_continuousMap_coordinateDerivative d i).comp
    (hF.prodMk measurable_const)
end EinsteinRelation.Sharpness
