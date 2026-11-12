import EinsteinRelation.Correctors.KernelDerivativeScaling
import EinsteinRelation.Correctors.HeatTransferIdentity
import EinsteinRelation.Correctors.StationaryKernelConvolution
import EinsteinRelation.Calculus.WeakCalculusAlgebra
import EinsteinRelation.Entropy.EllipticRegularity

/-! # Weak derivatives of compact-kernel convolutions

Source: `paper/main.tex:1028–1041`. The derivatives of a convolution are
realized on the full weak horizontal test domain, for arbitrary measurable
stationary `L²` fields. No orbitwise boundedness of the field is required.
-/

open MeasureTheory

noncomputable section

namespace EinsteinRelation.Correctors

open Entropy

variable {d : ℕ}

/-- The horizontal gradient of convolution uses the negative spatial
derivative, since translations occur with a positive sign
(`paper/main.tex:1028–1041`). -/
def kernelGradient (K : Vec d → ℝ) (f : FieldPair d → ℝ)
    (ω : FieldPair d) : Vec d :=
  fun i => -horizontalMollify (coordinateDerivative i K) f ω

/-- Integration by parts for the convolution against a concrete horizontal
test (`paper/main.tex:1028–1041`). -/
theorem integral_reflectedMollify_mul_derivative {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) {K : Vec d → ℝ}
    (hK : ContDiff ℝ (⊤ : ℕ∞) K) (hKc : HasCompactSupport K)
    {f : FieldPair d → ℝ} (hf : Measurable f) (hf2 : MemLp f 2 Q)
    (i : Fin d) {H : FieldPair d → ℝ} (hH : IsHorizontalTest H) :
    (∫ ω, horizontalMollify (reflectKernel K) f ω * horizontalDerivative i H ω ∂Q) =
      -(∫ ω, horizontalMollify (reflectKernel (coordinateDerivative i K)) f ω * H ω ∂Q) := by
  have hKr := contDiff_reflectKernel hK
  have hKrc := hasCompactSupport_reflectKernel hKc
  obtain ⟨B, -, hB⟩ := hH.bound_orbit
  have hHB : ∀ ω, |H ω| ≤ B := fun ω => by simpa using hB ω 0
  have hH2 : MemLp H 2 Q := memLp_of_ae_bound' hH.1 (ae_of_all _ hHB) 2
  have h1 := integral_horizontalMollify_mul_eq_L2 hQ hKr.continuous.measurable
    (hKr.continuous.integrable_of_hasCompactSupport hKrc) hf hf2
    (hH.measurable_derivative i) (hH.memLp_derivative Q 2 i)
  rw [reflectKernel_reflectKernel] at h1
  have h2 : ∀ ω, horizontalMollify K (horizontalDerivative i H) ω =
      -horizontalMollify (coordinateDerivative i K) H ω := fun ω => by
    rw [← horizontalDerivative_horizontalMollify_eq hK hKc hH i ω,
      horizontalMollify_horizontalDerivative_formula hK hKc hH.1 ⟨B, hHB⟩ i ω]
    rfl
  have hD := KernelCalculus.contDiff_coordinateIterate hK [i]
  have hDc := KernelCalculus.hasCompactSupport_coordinateIterate hKc [i]
  have hDr := contDiff_reflectKernel hD
  have hDrc := hasCompactSupport_reflectKernel hDc
  have h3 := integral_horizontalMollify_mul_eq_L2 hQ hDr.continuous.measurable
    (hDr.continuous.integrable_of_hasCompactSupport hDrc) hf hf2 hH.1 hH2
  rw [reflectKernel_reflectKernel] at h3
  simp only [coordinateIterate] at h3
  rw [h1, h3, ← integral_neg]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  change f ω * horizontalMollify K (horizontalDerivative i H) ω =
    -(f ω * horizontalMollify (coordinateDerivative i K) H ω)
  rw [h2]
  ring

/-- Weak differentiation of an arbitrary compact smooth convolution
(`paper/main.tex:1028–1041`). -/
theorem hasWeakHorizontalGradient_horizontalMollify {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) {K : Vec d → ℝ}
    (hK : ContDiff ℝ (⊤ : ℕ∞) K) (hKc : HasCompactSupport K)
    {f : FieldPair d → ℝ} (hf : Measurable f) (hf2 : MemLp f 2 Q) :
    HasWeakHorizontalGradient Q hQ (horizontalMollify K f) (kernelGradient K f) := by
  have hKi : Integrable K volume := hK.continuous.integrable_of_hasCompactSupport hKc
  have hD (i : Fin d) := KernelCalculus.contDiff_coordinateIterate hK [i]
  have hDi (i : Fin d) := KernelCalculus.integrable_coordinateIterate hK hKc [i]
  refine hasWeakHorizontalGradient_of_tests hQ
    (measurable_horizontalMollify _ hK.continuous.measurable hf)
    (memLp_horizontalMollify hQ one_le_two (by simp) hK.continuous.measurable hKi hf hf2)
    (measurable_pi_lambda _ fun i =>
      (measurable_horizontalMollify _ (hD i).continuous.measurable hf).neg)
    (fun i => (memLp_horizontalMollify hQ one_le_two (by simp)
      (hD i).continuous.measurable (hDi i) hf hf2).neg) ?_
  intro i H hH
  have h := integral_reflectedMollify_mul_derivative hQ (contDiff_reflectKernel hK)
    (hasCompactSupport_reflectKernel hKc) hf hf2 i hH
  rw [reflectKernel_reflectKernel] at h
  have hreflection : reflectKernel (coordinateDerivative i (reflectKernel K)) =
      fun x => -coordinateDerivative i K x := by
    funext x
    simp only [reflectKernel, coordinateDerivative_reflectKernel (hK.differentiable (by simp)),
      neg_neg]
  simpa only [hreflection, horizontalMollify_neg_kernel, kernelGradient] using h

/-- The second horizontal derivative has positive spatial sign
(`paper/main.tex:1033–1041`). The first index labels the differentiated
gradient component and the second its weak gradient. -/
def kernelHessian (K : Vec d → ℝ) (f : FieldPair d → ℝ)
    (ω : FieldPair d) (j : Fin d) : Vec d :=
  fun i => horizontalMollify (coordinateDerivative i (coordinateDerivative j K)) f ω

/-- Each component of the convolution gradient has the expected weak
gradient (`paper/main.tex:1033–1041`). -/
theorem hasWeakHorizontalGradient_kernelGradient {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) {K : Vec d → ℝ}
    (hK : ContDiff ℝ (⊤ : ℕ∞) K) (hKc : HasCompactSupport K)
    {f : FieldPair d → ℝ} (hf : Measurable f) (hf2 : MemLp f 2 Q) (j : Fin d) :
    HasWeakHorizontalGradient Q hQ (fun ω => kernelGradient K f ω j)
      (fun ω => kernelHessian K f ω j) := by
  have h := (hasWeakHorizontalGradient_horizontalMollify hQ
    (KernelCalculus.contDiff_coordinateIterate hK [j])
    (KernelCalculus.hasCompactSupport_coordinateIterate hKc [j]) hf hf2).smul (-1)
  simp only [coordinateIterate, neg_one_mul] at h
  have heq : (fun ω => (-1 : ℝ) • kernelGradient (coordinateDerivative j K) f ω) =
      fun ω => kernelHessian K f ω j := by
    funext ω i
    simp [kernelGradient, kernelHessian]
  rw [heq] at h
  exact h

/-- Componentwise weak gradients give the divergence by their trace
(`paper/main.tex:1028–1041`). -/
theorem hasWeakHorizontalDivergence_of_component_gradients
    {Q : Measure (FieldPair d)} {hQ : IsStationary Q}
    {V : FieldPair d → Vec d} {DV : Fin d → FieldPair d → Vec d}
    (hV : ∀ i, HasWeakHorizontalGradient Q hQ (fun ω => V ω i) (DV i)) :
    HasWeakHorizontalDivergence Q hQ V (fun ω => ∑ i, DV i ω i) := by
  refine ⟨fun i => (hV i).1,
    integrable_finset_sum _ fun i _ => (hV i).2.1 i, fun F hF DF hDF => ?_⟩
  obtain ⟨B, hB⟩ := ae_bound_of_isHorizontallySmoothTest hF
  have hleft (i : Fin d) : Integrable (fun ω => V ω i * DF i ω) Q := by
    obtain ⟨C, hC⟩ := ae_bound_of_hasHorizontalLpDerivative hF (hDF i)
    exact integrable_mul_of_ae_bound (hV i).1 hC
  have hright (i : Fin d) : Integrable (fun ω => DV i ω i * F ω) Q :=
    integrable_mul_of_ae_bound ((hV i).2.1 i) hB
  rw [integral_finset_sum _ fun i _ => hleft i]
  simp_rw [(hV _).2.2 _ F _ hF (hDF _)]
  rw [Finset.sum_neg_distrib, ← integral_finset_sum _ fun i _ => hright i]
  simp only [Finset.sum_mul]

/-- The spatial Laplacian kernel is the weak horizontal divergence of the
convolution gradient (`paper/main.tex:1021–1025`). -/
theorem hasWeakHorizontalDivergence_kernelGradient {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) {K : Vec d → ℝ}
    (hK : ContDiff ℝ (⊤ : ℕ∞) K) (hKc : HasCompactSupport K)
    {f : FieldPair d → ℝ} (hf : Measurable f) (hf2 : MemLp f 2 Q) :
    HasWeakHorizontalDivergence Q hQ (kernelGradient K f)
      (horizontalMollify (coordLaplacian K) f) := by
  have h := hasWeakHorizontalDivergence_of_component_gradients
    (fun i => hasWeakHorizontalGradient_kernelGradient hQ hK hKc hf hf2 i)
  refine Entropy.HasWeakHorizontalDivergence.congr_div h ?_
  have hi : ∀ᵐ ω ∂Q, ∀ i : Fin d,
      Integrable (fun z => coordinateIterate [i, i] K z * f (translate z ω)) volume :=
    ae_all_iff.mpr fun i => ae_integrable_kernel_translate hQ
      (KernelCalculus.contDiff_coordinateIterate hK [i, i]).continuous.measurable
      (KernelCalculus.integrable_coordinateIterate hK hKc [i, i]) hf
      (hf2.integrable one_le_two)
  filter_upwards [hi] with ω hω
  simp only [kernelHessian, horizontalMollify, coordLaplacian, coordinateDerivative,
    Finset.sum_mul]
  exact (integral_finset_sum _ fun i _ => hω i).symm

end EinsteinRelation.Correctors
