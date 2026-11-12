import EinsteinRelation.Correctors.CoefficientColumnDivergence
import EinsteinRelation.Environment.CoefficientFieldRescaling

/-! # Measurable initial divergence

Source: `paper/main.tex:787–792,850–852`. The literal Fréchet derivative
expression is measurable jointly in the continuous coefficient field and
space, including points where differentiability fails.
-/

open MeasureTheory
namespace EinsteinRelation.Correctors

/-- The literal coefficient-column divergence is jointly Borel measurable
in a continuous coefficient and its spatial argument.
Source: `paper/main.tex:787–792,850–852`. -/
theorem measurable_coefficient_column_divergence (d : ℕ) (i : Fin d) :
    Measurable (fun z : CoefficientField d × Vec d =>
      divergence (fun x j => z.1 x j i) z.2) := by
  unfold divergence coordinateDerivative
  apply Finset.measurable_sum
  intro j _
  exact measurable_fderiv_apply_const_with_param ℝ
    (f := fun a : CoefficientField d => fun x => a x j i)
    (continuous_eval.matrix_elem j i) (unitVector j)

end EinsteinRelation.Correctors
