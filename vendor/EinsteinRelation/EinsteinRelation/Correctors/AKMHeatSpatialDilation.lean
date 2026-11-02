import EinsteinRelation.Correctors.HeatKernelScaling
import EinsteinRelation.Correctors.KernelDerivativeScaling
import EinsteinRelation.Correctors.HeatSelectedSkewMeaningSupport

/-!
# Spatial dilation of the literal AKM heat formula

Source: `paper/main.tex:716,748`. Differentiating the rescaled Gaussian
contributes two inverse length factors. The full-space integral cancels
its volume factor. These identities concern the actual kernels and
integrals; transport of the time-cutoff convergence is a separate step.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors
open HeatSelectedSkewMeaning KernelCalculus

private theorem centered_heat_second_dilation {d : ℕ}
    (c t : ℝ) (hc : 0 < c) (ht : 0 < t) (i j : Fin d) (x y : Vec d) :
    coordinateDerivative j (coordinateDerivative i
      (fun w => euclideanHeatKernel (c ^ 2 * t) (c • y - w))) (c • x) =
      (c ^ d)⁻¹ * (c⁻¹) ^ 2 *
        coordinateDerivative j (coordinateDerivative i
          (fun w => euclideanHeatKernel t (y - w))) x := by
  have hf : ContDiff ℝ (⊤ : ℕ∞)
      (fun w : Vec d => euclideanHeatKernel t (y - w)) :=
    (contDiff_euclideanHeatKernel t).comp (contDiff_const.sub contDiff_id)
  have heq : (fun w : Vec d => euclideanHeatKernel (c ^ 2 * t) (c • y - w)) =
      (fun w => (c ^ d)⁻¹ * euclideanHeatKernel t (y - c⁻¹ • w)) := by
    funext w
    have hw : c • (y - c⁻¹ • w) = c • y - w := by
      rw [smul_sub, smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
    rw [← hw, euclideanHeatKernel_scale hc ht]
  rw [heq]
  have h := congrFun (coordinateIterate_const_mul_comp_smul hf [j, i]
    ((c ^ d)⁻¹) c⁻¹) (c • x)
  simpa only [coordinateIterate, List.length_cons, List.length_nil,
    Nat.zero_add, Nat.reduceAdd, smul_smul, inv_mul_cancel₀ hc.ne', one_smul] using h

/-- Exact physical space/time scaling of the twice differentiated Gaussian
in AKM (6.7). The source amplitude is an arbitrary scalar. -/
theorem akmHeatGradientDensity_dilation {d : ℕ}
    (g : Vec d → Vec d) (c b t : ℝ) (hc : 0 < c) (ht : 0 < t)
    (j k l : Fin d) (x y : Vec d) :
    akmHeatGradientDensity (fun z => b • g (c⁻¹ • z))
        (c ^ 2 * t) j k l (c • x) (c • y) =
      ((c ^ d)⁻¹ * (b * (c⁻¹) ^ 2)) *
        akmHeatGradientDensity g t j k l x y := by
  have hct : 0 < c ^ 2 * t := mul_pos (sq_pos_of_pos hc) ht
  unfold akmHeatGradientDensity
  simp only [dif_pos ht, dif_pos hct]
  change (b • g (c⁻¹ • (c • y))) k *
      coordinateDerivative l (coordinateDerivative j
        (fun w => euclideanHeatKernel (c ^ 2 * t) (c • y - w))) (c • x) -
    (b • g (c⁻¹ • (c • y))) j *
      coordinateDerivative l (coordinateDerivative k
        (fun w => euclideanHeatKernel (c ^ 2 * t) (c • y - w))) (c • x) =
    _ * (g y k * coordinateDerivative l (coordinateDerivative j
      (fun w => euclideanHeatKernel t (y - w))) x -
      g y j * coordinateDerivative l (coordinateDerivative k
        (fun w => euclideanHeatKernel t (y - w))) x)
  rw [centered_heat_second_dilation c t hc ht,
    centered_heat_second_dilation c t hc ht]
  simp only [smul_smul, inv_mul_cancel₀ hc.ne', one_smul, Pi.smul_apply, smul_eq_mul]
  ring

/-- The Jacobian of the spatial heat integral cancels the Gaussian volume
factor, leaving only the source amplitude and two derivative factors. -/
theorem akmHeatGradientSpaceIntegral_dilation {d : ℕ}
    (g : Vec d → Vec d) (c b t : ℝ) (hc : 0 < c) (ht : 0 < t)
    (j k l : Fin d) (x : Vec d) :
    akmHeatGradientSpaceIntegral (fun z => b • g (c⁻¹ • z))
        (c ^ 2 * t) j k l (c • x) =
      (b * (c⁻¹) ^ 2) * akmHeatGradientSpaceIntegral g t j k l x := by
  have h := Measure.integral_comp_smul (volume : Measure (Vec d))
    (fun y => akmHeatGradientDensity (fun z => b • g (c⁻¹ • z))
      (c ^ 2 * t) j k l (c • x) y) c
  simp only [Module.finrank_pi, Fintype.card_fin, smul_eq_mul,
    abs_of_pos (inv_pos.mpr (pow_pos hc d))] at h
  simp_rw [akmHeatGradientDensity_dilation g c b t hc ht j k l x] at h
  rw [integral_const_mul] at h
  apply mul_left_cancel₀ (inv_ne_zero (pow_ne_zero _ hc.ne'))
  change (c ^ d)⁻¹ * (∫ y, _) = (c ^ d)⁻¹ * (_ * ∫ y, _)
  rw [← h]
  ring

end EinsteinRelation.Correctors
