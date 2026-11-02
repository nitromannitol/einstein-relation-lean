import EinsteinRelation.Correctors.HeatKernelMixedHessian
import EinsteinRelation.Correctors.StationaryKernelConvolution

/-!
# The source heat-gradient density as a stationary convolution

Source: `paper/main.tex:716,748`. The two derivatives of the centered
Gaussian are the ordinary mixed Hessian at the relative spatial argument.
-/
open MeasureTheory
namespace EinsteinRelation.Correctors
open HeatSelectedSkewMeaning

private theorem euclideanHeatKernel_sub_comm {d : ℕ} (t : ℝ) (x y : Vec d) :
    euclideanHeatKernel t (y - x) = euclideanHeatKernel t (x - y) := by
  have hs : euclideanSq (y - x) = euclideanSq (x - y) := by
    unfold euclideanSq dot
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.sub_apply]
    ring
  simp only [euclideanHeatKernel, hs]

/-- Twice differentiating the centered Gaussian gives its ordinary Hessian. -/
theorem centeredHeatKernel_secondDerivative {d : ℕ} (t : ℝ)
    (i j : Fin d) (x y : Vec d) :
    coordinateDerivative j (coordinateDerivative i
      (fun w => euclideanHeatKernel t (y - w))) x =
      coordinateDerivative j (coordinateDerivative i
        (euclideanHeatKernel (d := d) t)) (x - y) := by
  have heq : (fun w => euclideanHeatKernel t (y - w)) =
      (fun w => euclideanHeatKernel t (w - y)) :=
    funext fun w => euclideanHeatKernel_sub_comm t w y
  rw [heq]
  have hfirst : coordinateDerivative i (fun w => euclideanHeatKernel t (w - y)) =
      fun w => coordinateDerivative i (euclideanHeatKernel t) (w - y) := by
    funext w
    unfold coordinateDerivative
    rw [fderiv_comp_sub]
  rw [hfirst]
  exact congrArg (fun A : Vec d →L[ℝ] ℝ => A (unitVector j))
    (fderiv_comp_sub (𝕜 := ℝ) (f := coordinateDerivative i
      (euclideanHeatKernel (d := d) t)) (x := x) y)

/-- The literal source density is a difference of two mixed-Hessian
convolution integrands, with exactly its original row and column signs. -/
theorem akmHeatGradientDensity_eq_mixedHessian {d : ℕ} (g : Vec d → Vec d)
    (t : ℝ) (ht : 0 < t) (j k l : Fin d) (x y : Vec d) :
    akmHeatGradientDensity g t j k l x y =
      g y k * coordinateDerivative l (coordinateDerivative j
        (euclideanHeatKernel (d := d) t)) (x - y) -
      g y j * coordinateDerivative l (coordinateDerivative k
        (euclideanHeatKernel (d := d) t)) (x - y) := by
  unfold akmHeatGradientDensity
  rw [dif_pos ht]
  change g y k * coordinateDerivative l (coordinateDerivative j
      (fun w => euclideanHeatKernel t (y - w))) x -
    g y j * coordinateDerivative l (coordinateDerivative k
      (fun w => euclideanHeatKernel t (y - w))) x = _
  rw [centeredHeatKernel_secondDerivative, centeredHeatKernel_secondDerivative]

/-- The spatial source heat integral at the origin is the difference of
stationary convolutions whenever its two terms are genuinely integrable. -/
theorem akmHeatGradientSpaceIntegral_eq_horizontalMollify {d : ℕ}
    (F : FieldPair d → Vec d) (ρ : FieldPair d)
    (t : ℝ) (ht : 0 < t) (j k l : Fin d)
    (hk : Integrable (fun y : Vec d => F (translate y ρ) k *
      coordinateDerivative l (coordinateDerivative j
        (euclideanHeatKernel (d := d) t)) (-y)) volume)
    (hj : Integrable (fun y : Vec d => F (translate y ρ) j *
      coordinateDerivative l (coordinateDerivative k
        (euclideanHeatKernel (d := d) t)) (-y)) volume) :
    akmHeatGradientSpaceIntegral (fun y => F (translate y ρ)) t j k l 0 =
      horizontalMollify
        (fun y => coordinateDerivative l (coordinateDerivative j
          (euclideanHeatKernel (d := d) t)) (-y)) (fun ω => F ω k) ρ -
      horizontalMollify
        (fun y => coordinateDerivative l (coordinateDerivative k
          (euclideanHeatKernel (d := d) t)) (-y)) (fun ω => F ω j) ρ := by
  unfold akmHeatGradientSpaceIntegral
  simp_rw [akmHeatGradientDensity_eq_mixedHessian _ t ht, zero_sub]
  rw [integral_sub hk hj]
  simp only [horizontalMollify, mul_comm]

end EinsteinRelation.Correctors
