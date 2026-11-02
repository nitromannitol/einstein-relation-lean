import EinsteinRelation.Correctors.HeatKernelMixedHessian
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Source: `paper/main.tex:716,748`. Exact parabolic dilation of the
Gaussian Hessian and its genuine spatial L¹ integral. -/
open MeasureTheory
namespace EinsteinRelation.Correctors

/-- A Gaussian mixed Hessian has parabolic degree `-d-2`. -/
theorem heatKernel_mixedHessian_scale {d : ℕ} (c t : ℝ)
    (hc : 0 < c) (ht : 0 < t) (i j : Fin d) (x : Vec d) :
    coordinateDerivative j (coordinateDerivative i
      (euclideanHeatKernel (d := d) (c ^ 2 * t))) (c • x) =
      ((c ^ d)⁻¹ * (c ^ 2)⁻¹) * coordinateDerivative j
        (coordinateDerivative i (euclideanHeatKernel (d := d) t)) x := by
  rw [coordinateDerivative_two_euclideanHeatKernel _ (by positivity),
    coordinateDerivative_two_euclideanHeatKernel _ ht, euclideanHeatKernel_scale hc ht]
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases hij : i = j
  · simp only [if_pos hij]
    field_simp
  · simp only [if_neg hij]
    field_simp
    ring

/-- Integrability and the L¹ mass of a mixed Hessian transport with the
inverse square dilation factor. -/
theorem integrable_heatKernel_mixedHessian_scale {d : ℕ} (c t : ℝ)
    (hc : 0 < c) (ht : 0 < t) (i j : Fin d)
    (hH : Integrable (coordinateDerivative j (coordinateDerivative i
      (euclideanHeatKernel (d := d) t))) volume) :
    Integrable (coordinateDerivative j (coordinateDerivative i
      (euclideanHeatKernel (d := d) (c ^ 2 * t)))) volume ∧
      (∫ x, |coordinateDerivative j (coordinateDerivative i
        (euclideanHeatKernel (d := d) (c ^ 2 * t))) x| ∂volume) =
        (c ^ 2)⁻¹ * ∫ x, |coordinateDerivative j (coordinateDerivative i
          (euclideanHeatKernel (d := d) t)) x| ∂volume := by
  have hfun : (coordinateDerivative j (coordinateDerivative i
      (euclideanHeatKernel (d := d) (c ^ 2 * t)))) =
      (fun x => ((c ^ d)⁻¹ * (c ^ 2)⁻¹) * coordinateDerivative j
        (coordinateDerivative i (euclideanHeatKernel (d := d) t)) (c⁻¹ • x)) := by
    funext x
    simpa only [smul_smul, mul_inv_cancel₀ hc.ne', one_smul] using
      heatKernel_mixedHessian_scale c t hc ht i j (c⁻¹ • x)
  rw [hfun]
  constructor
  · exact (hH.comp_smul (inv_ne_zero hc.ne')).const_mul _
  · simp_rw [abs_mul, abs_inv, abs_pow, abs_of_pos hc]
    rw [integral_const_mul]
    have hchange := Measure.integral_comp_inv_smul_of_nonneg volume
      (fun x : Vec d => |coordinateDerivative j
        (coordinateDerivative i (euclideanHeatKernel (d := d) t)) x|) hc.le
    simp only [Module.finrank_fin_fun, smul_eq_mul] at hchange
    rw [hchange]
    field_simp

end EinsteinRelation.Correctors
