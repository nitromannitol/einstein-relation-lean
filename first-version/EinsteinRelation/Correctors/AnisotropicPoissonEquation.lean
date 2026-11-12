import EinsteinRelation.Correctors.AnisotropicKernelWeakCalculus
import EinsteinRelation.Correctors.MatrixHessianTrace
import EinsteinRelation.Correctors.KernelDerivativeConstants

/-! # The homogenized Poisson equation of the anisotropic bands

Source: `paper/main.tex:1009–1025`. The actual whitened kernel solves the
constant-coefficient equation with its factor `1/2` accounted for exactly.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors

/-- Whitening reduces the transformed spatial operator to the radial one
(`paper/main.tex:1009–1018`). -/
theorem matrixLaplacian_const_comp_linear {d : ℕ} (A : Mat d)
    (B : Vec d →L[ℝ] Vec d) (c : ℝ) {K : Vec d → ℝ}
    (hK : ContDiff ℝ (⊤ : ℕ∞) K)
    (hBA : let M : Mat d := fun i j => B (unitVector j) i
      M * A * M.transpose = 1) (x : Vec d) :
    matrixLaplacian A (fun y => c * K (B y)) x = c * coordLaplacian K (B x) := by
  let M : Mat d := fun i j => B (unitVector j) i
  have hd (i j : Fin d) :
      coordinateIterate [i, j] (fun y => c * K (B y)) x =
      c * (∑ a, ∑ b, M a j * M b i * coordinateIterate [b, a] K (B x)) := by
    have he := congrFun (KernelCalculus.coordinateIterate_const_mul
      (hK.comp B.contDiff) [i, j] c) x
    change coordinateIterate [i, j] (fun y => c * K (B y)) x =
      c * coordinateIterate [i, j] (fun y => K (B y)) x at he
    rw [he, KernelCalculus.coordinateIterate_two_comp_linear hK B]
  calc
    _ = c * (∑ i, ∑ j, A i j *
        (∑ a, ∑ b, M a j * M b i * coordinateIterate [b, a] K (B x))) := by
      simp only [matrixLaplacian, hd, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = _ := by
      rw [KernelCalculus.matrix_hessian_contraction_trace A M
        (fun b a => coordinateIterate [b, a] K (B x)) hBA]
      rfl

/-- The compact anisotropic band has twice the dyadic averaging source
(`paper/main.tex:1009–1025`). -/
theorem matrixLaplacian_anisotropicBandKernel {d : ℕ} (hd : 2 ≤ d)
    (A : Mat d) (B : Vec d ≃L[ℝ] Vec d)
    (hBA : let M : Mat d := fun i j => B (unitVector j) i
      M * A * M.transpose = 1)
    {r : ℝ} (hr : 0 < r) (x : Vec d) :
    matrixLaplacian A (anisotropicBandKernel B r) x =
      2 * (anisotropicAverage B r x - anisotropicAverage B (2 * r) x) := by
  change matrixLaplacian A (fun y => (2 * |B.toContinuousLinearMap.det|) * radialBandKernel d r (B y)) x = _
  have he := matrixLaplacian_const_comp_linear A B.toContinuousLinearMap
    (2 * |B.toContinuousLinearMap.det|) (radialBandKernel_contDiff hd hr) hBA x
  change matrixLaplacian A (fun y => (2 * |B.toContinuousLinearMap.det|) *
    radialBandKernel d r (B y)) x =
      (2 * |B.toContinuousLinearMap.det|) * coordLaplacian (radialBandKernel d r) (B x) at he
  rw [he, coordLaplacian_radialBandKernel hd hr]
  simp only [anisotropicAverage]
  ring

/-- The actual anisotropic convolution solves its homogenized weak
Poisson equation (`paper/main.tex:1019–1025`). -/
theorem hasWeakHorizontalDivergence_anisotropicBand {d : ℕ}
    {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) (hd : 2 ≤ d) (A : Mat d) (B : Vec d ≃L[ℝ] Vec d)
    (hBA : let M : Mat d := fun i j => B (unitVector j) i
      M * A * M.transpose = 1)
    {r : ℝ} (hr : 0 < r) {f : FieldPair d → ℝ}
    (hf : Measurable f) (hf2 : MemLp f 2 Q) :
    HasWeakHorizontalDivergence Q hQ
      (fun ω => A.mulVec (kernelGradient (anisotropicBandKernel B r) f ω))
      (fun ω => 2 * (horizontalMollify (anisotropicAverage B r) f ω -
        horizontalMollify (anisotropicAverage B (2 * r)) f ω)) := by
  have h := hasWeakHorizontalDivergence_matrix_kernelGradient hQ A
    (anisotropicBandKernel_contDiff hd B hr) (anisotropicBandKernel_hasCompactSupport hd B hr) hf hf2
  apply Entropy.HasWeakHorizontalDivergence.congr_div h
  have hfun : matrixLaplacian A (anisotropicBandKernel B r) =
      fun x => 2 * (anisotropicAverage B r x - anisotropicAverage B (2 * r) x) :=
    funext (matrixLaplacian_anisotropicBandKernel hd A B hBA hr)
  rw [hfun]
  have h2r : 0 < 2 * r := by positivity
  have hs := horizontalMollify_sub_kernel_ae hQ
    (anisotropicAverage_contDiff B hr).continuous.measurable
    ((anisotropicAverage_contDiff B hr).continuous.integrable_of_hasCompactSupport
      (anisotropicAverage_hasCompactSupport B hr))
    (anisotropicAverage_contDiff B h2r).continuous.measurable
    ((anisotropicAverage_contDiff B h2r).continuous.integrable_of_hasCompactSupport
      (anisotropicAverage_hasCompactSupport B h2r)) hf (hf2.integrable one_le_two)
  filter_upwards [hs] with ω hω
  change (∫ x, (2 * (anisotropicAverage B r x - anisotropicAverage B (2 * r) x)) *
    f (translate x ω)) = _
  simp_rw [mul_assoc]
  rw [integral_const_mul]
  exact congrArg (fun t : ℝ => 2 * t) hω

end EinsteinRelation.Correctors
