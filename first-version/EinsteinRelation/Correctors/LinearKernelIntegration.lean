import EinsteinRelation.Correctors.LinearKernelCalculus
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Function.Jacobian

/-! # Mass under the homogenized coordinate change

Source: `paper/main.tex:1003–1018`. The determinant normalization preserves
the integral of the actual spatial kernels.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors.KernelCalculus

/-- The normalized coordinate change preserves kernel mass
(`paper/main.tex:1003–1018`). -/
theorem integral_normalized_linear {d : ℕ} (B : Vec d ≃L[ℝ] Vec d)
    (f : Vec d → ℝ) :
    (∫ x : Vec d, |B.toContinuousLinearMap.det| * f (B x)) = ∫ x : Vec d, f x := by
  have h_image : (B : Vec d → Vec d) '' Set.univ = Set.univ := by
    ext x; simp
  have h := integral_image_eq_integral_abs_det_fderiv_smul volume
    MeasurableSet.univ
    (fun x hx => (B.toContinuousLinearMap.hasFDerivAt (x := x)).hasFDerivWithinAt)
    (fun x hx y hy h => B.injective h)
    f
  calc
    (∫ x : Vec d, |B.toContinuousLinearMap.det| * f (B x))
        = (∫ x : Vec d, |B.toContinuousLinearMap.det| • f (B x)) := by
      simp [smul_eq_mul]
    _ = (∫ x in Set.univ, |B.toContinuousLinearMap.det| • f (B x)) := by simp
    _ = (∫ x in (B : Vec d → Vec d) '' Set.univ, f x) := by
      simpa [h_image] using h.symm
    _ = (∫ x : Vec d, f x) := by simp [h_image]

end EinsteinRelation.Correctors.KernelCalculus
