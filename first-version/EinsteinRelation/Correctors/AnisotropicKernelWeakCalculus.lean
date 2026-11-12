import EinsteinRelation.Correctors.KernelConvolutionBands
import EinsteinRelation.Correctors.AnisotropicDyadicKernels

/-! # Weak homogenized equations for compact kernel convolutions

Source: `paper/main.tex:1019–1025,1044–1054`. A constant matrix passes
through the full weak horizontal divergence of a compact convolution.
-/

open MeasureTheory

noncomputable section

namespace EinsteinRelation.Correctors

variable {d : ℕ}

/-- The constant-coefficient spatial operator before its factor `1/2`
(`paper/main.tex:1019–1025`). -/
def matrixLaplacian (A : Mat d) (K : Vec d → ℝ) (x : Vec d) : ℝ :=
  ∑ i, ∑ j, A i j * coordinateIterate [i, j] K x

/-- The constant matrix times the convolution gradient has the exact
spatial operator as weak divergence (`paper/main.tex:1019–1025`). -/
theorem hasWeakHorizontalDivergence_matrix_kernelGradient {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) (A : Mat d) {K : Vec d → ℝ}
    (hK : ContDiff ℝ (⊤ : ℕ∞) K) (hKc : HasCompactSupport K)
    {f : FieldPair d → ℝ} (hf : Measurable f) (hf2 : MemLp f 2 Q) :
    HasWeakHorizontalDivergence Q hQ (fun ω => A.mulVec (kernelGradient K f ω))
      (horizontalMollify (matrixLaplacian A K) f) := by
  have hcomp (i : Fin d) :
      HasWeakHorizontalGradient Q hQ (fun ω => A.mulVec (kernelGradient K f ω) i)
        (fun ω => ∑ j, A i j • kernelHessian K f ω j) := by
    have h := HasWeakHorizontalGradient.finset_sum Finset.univ
      (fun j _ => (hasWeakHorizontalGradient_kernelGradient hQ hK hKc hf hf2 j).smul (A i j))
    simpa only [Matrix.mulVec, dotProduct, smul_eq_mul] using h
  have h := hasWeakHorizontalDivergence_of_component_gradients hcomp
  refine Entropy.HasWeakHorizontalDivergence.congr_div h ?_
  have hi : ∀ᵐ ω ∂Q, ∀ i j : Fin d,
      Integrable (fun z => coordinateIterate [i, j] K z * f (translate z ω)) volume :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => ae_integrable_kernel_translate hQ
      (KernelCalculus.contDiff_coordinateIterate hK [i, j]).continuous.measurable
      (KernelCalculus.integrable_coordinateIterate hK hKc [i, j]) hf
      (hf2.integrable one_le_two)
  filter_upwards [hi] with ω hω
  have hij (i j : Fin d) : Integrable
      (fun z => A i j * coordinateDerivative i (coordinateDerivative j K) z * f (translate z ω)) volume := by
    simpa only [mul_assoc] using (hω i j).const_mul (A i j)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, kernelHessian,
    horizontalMollify, matrixLaplacian, coordinateIterate, Finset.sum_mul]
  rw [integral_finset_sum Finset.univ (fun i _ =>
    integrable_finset_sum Finset.univ (fun j _ => hij i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finset_sum Finset.univ (fun j _ => hij i j)]
  apply Finset.sum_congr rfl
  intro j _
  simp only [mul_assoc, integral_const_mul]

end EinsteinRelation.Correctors
