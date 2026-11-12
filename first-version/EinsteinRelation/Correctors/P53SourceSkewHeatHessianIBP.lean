import EinsteinRelation.Correctors.HeatTransferIdentity
import EinsteinRelation.Correctors.HeatKernelConvolution
import EinsteinRelation.Correctors.HeatKernelMixedHessian

/-!
# Integration by parts for the heat-kernel Hessian

Source: `paper/main.tex:740-756`, AKM (6.7). The two spatial derivatives of the
heat-kernel Hessian move onto a smooth compactly supported test function.
-/
open MeasureTheory Filter Topology
namespace EinsteinRelation.Correctors

/-- Translation covariance of a coordinate derivative: differentiating `z ↦ f (z - y)`
in direction `i` is differentiating `f` at `x - y`. -/
theorem coordinateDerivative_comp_sub_apply {d : ℕ} (f : Vec d → ℝ) (i : Fin d) (y x : Vec d) :
    coordinateDerivative i (fun z => f (z - y)) x = coordinateDerivative i f (x - y) := by
  unfold coordinateDerivative
  rw [fderiv_comp_sub]

/-- One integration by parts in a coordinate direction, moving the derivative off `g`
onto a compactly supported `C¹` factor `f`. -/
theorem integral_mul_coordinateDerivative_eq_neg {d : ℕ} {f g : Vec d → ℝ} {i : Fin d}
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) (hg : ContDiff ℝ 1 g) :
    ∫ x, f x * coordinateDerivative i g x = -∫ x, coordinateDerivative i f x * g x := by
  unfold coordinateDerivative
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (integrable_mul_of_compact_support (continuous_fderiv_dir hf (unitVector i))
      (hfc.fderiv_apply ℝ (unitVector i)) hg.continuous)
    (integrable_mul_of_compact_support hf.continuous hfc (continuous_fderiv_dir hg (unitVector i)))
    (integrable_mul_of_compact_support hf.continuous hfc hg.continuous)
    (hf.differentiable le_rfl) (hg.differentiable le_rfl)

/-- `∫ ψ(x) ∂_l∂_jΦ_t(x - y) dx = (Φ_t ⋆ ∂_j∂_lψ)(y)` for smooth compactly supported
`ψ`. Source: AKM (6.7), `paper/main.tex:740-756`. -/
theorem integral_mul_heatHessian_eq_heatKernelConvolution {d : ℕ} {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) {t : ℝ} (ht : 0 < t)
    (j l : Fin d) (y : Vec d) :
    (∫ x, ψ x * coordinateDerivative l (coordinateDerivative j
      (euclideanHeatKernel (d := d) t)) (x - y)) =
      heatKernelConvolution t (coordinateDerivative j (coordinateDerivative l ψ)) y := by
  have hψ2 : ContDiff ℝ 2 ψ := hψ.of_le (by norm_cast)
  have hψ1 : ContDiff ℝ 1 ψ := hψ2.of_le one_le_two
  -- The translated kernel `φ(z) = Φ_t(z - y)` and its first coordinate derivative.
  have hφ2 : ContDiff ℝ 2 (fun z => euclideanHeatKernel (d := d) t (z - y)) :=
    (contDiff_two_euclideanHeatKernel t).comp (contDiff_id.sub contDiff_const)
  have hφ1 : ContDiff ℝ 1 (fun z => euclideanHeatKernel (d := d) t (z - y)) :=
    hφ2.of_le one_le_two
  have hjφ1 : ContDiff ℝ 1
      (coordinateDerivative j (fun z => euclideanHeatKernel (d := d) t (z - y))) :=
    contDiff_one_fderiv_dir hφ2 (unitVector j)
  have hlψ1 : ContDiff ℝ 1 (coordinateDerivative l ψ) :=
    contDiff_one_fderiv_dir hψ2 (unitVector l)
  have hlψc : HasCompactSupport (coordinateDerivative l ψ) :=
    hψc.fderiv_apply ℝ (unitVector l)
  -- Move the translation through the coordinate derivative.
  have hF : coordinateDerivative j (fun z => euclideanHeatKernel (d := d) t (z - y)) =
      fun z => coordinateDerivative j (euclideanHeatKernel (d := d) t) (z - y) :=
    funext fun z => coordinateDerivative_comp_sub_apply (euclideanHeatKernel (d := d) t) j y z
  have hF2 : ∀ x, coordinateDerivative l
      (coordinateDerivative j (fun z => euclideanHeatKernel (d := d) t (z - y))) x =
      coordinateDerivative l (coordinateDerivative j (euclideanHeatKernel (d := d) t))
        (x - y) := by
    intro x
    rw [hF]
    exact coordinateDerivative_comp_sub_apply (coordinateDerivative j
      (euclideanHeatKernel (d := d) t)) l y x
  -- Two integrations by parts: first in direction `l` against `ψ`, then in `j`.
  have h1 := integral_mul_coordinateDerivative_eq_neg (f := ψ) (i := l) hψ1 hψc hjφ1
  have h2 := integral_mul_coordinateDerivative_eq_neg (f := coordinateDerivative l ψ) (i := j)
    hlψ1 hlψc hφ1
  rw [heatKernelConvolution, if_neg ht.ne']
  have hL : (fun x => ψ x * coordinateDerivative l
      (coordinateDerivative j (euclideanHeatKernel (d := d) t)) (x - y)) =
      fun x => ψ x * coordinateDerivative l
        (coordinateDerivative j (fun z => euclideanHeatKernel (d := d) t (z - y))) x :=
    funext fun x => by rw [hF2 x]
  rw [hL, h1, h2, neg_neg]

end EinsteinRelation.Correctors
