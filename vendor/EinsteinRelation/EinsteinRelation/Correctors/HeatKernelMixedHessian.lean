import EinsteinRelation.Correctors.HeatKernelScaling
import EinsteinRelation.Correctors.HeatSelectedSkewMeaningSupport

/-! Gaussian calculus for the physical transport at `paper/main.tex:716,748`. -/
namespace EinsteinRelation.Correctors

open EinsteinRelation

/-- The uncentered Gaussian's mixed coordinate Hessian. -/
theorem coordinateDerivative_two_euclideanHeatKernel {d : ℕ}
    (t : ℝ) (_ht : 0 < t) (i j : Fin d) (x : Vec d) :
    coordinateDerivative j (coordinateDerivative i (euclideanHeatKernel t)) x =
      euclideanHeatKernel t x * (x i * x j / (4 * t ^ 2) -
        (if i = j then 1 / (2 * t) else 0)) := by
  have hdiff : Differentiable ℝ (euclideanHeatKernel (d := d) t) :=
    (contDiff_euclideanHeatKernel t).differentiable (by simp)
  unfold coordinateDerivative
  have hinner : (fun y : Vec d => fderiv ℝ (euclideanHeatKernel (d := d) t) y (unitVector i)) =
      fun y => euclideanHeatKernel t y * (-(1 / (2 * t)) * y i) := by
    ext y
    rw [fderiv_euclideanHeatKernel t y (unitVector i)]
    have hsum : (∑ k, y k * unitVector i k) = y i := by
      simp [unitVector, Pi.single_apply, Finset.sum_ite_eq', Finset.mem_univ]
    simp [hsum]
  rw [hinner]
  have hprod_deriv : HasFDerivAt (fun y : Vec d => -(1 / (2 * t)) * y i)
      (-(1 / (2 * t)) • (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ)) x :=
    (hasFDerivAt_apply (𝕜 := ℝ) i x).const_mul _
  have hG : HasFDerivAt (fun y : Vec d => euclideanHeatKernel t y * (-(1 / (2 * t)) * y i))
      (euclideanHeatKernel t x • (-(1 / (2 * t)) • (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ)) +
        (-(1 / (2 * t)) * x i) • fderiv ℝ (euclideanHeatKernel (d := d) t) x) x :=
    (hdiff x).hasFDerivAt.fun_mul hprod_deriv
  rw [hG.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [fderiv_euclideanHeatKernel t x (unitVector j)]
  have hsumj : (∑ k, x k * unitVector j k) = x j := by
    simp [unitVector, Pi.single_apply, Finset.sum_ite_eq', Finset.mem_univ]
  simp [hsumj]
  by_cases hij : i = j
  · subst hij
    simp [unitVector]
    ring
  · have hne_ji : unitVector j i = 0 := by
      simp [unitVector, Ne.symm hij]
    simp [hij, hne_ji]
    ring

end EinsteinRelation.Correctors
