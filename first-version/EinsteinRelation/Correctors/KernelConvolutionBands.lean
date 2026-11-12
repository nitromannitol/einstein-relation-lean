import EinsteinRelation.Correctors.KernelWeakCalculus
import EinsteinRelation.Correctors.RadialDyadicKernels
import EinsteinRelation.Calculus.WeakHorizontalFiniteSums

/-! # Local weak Poisson bands from compact kernels

Source: `paper/main.tex:1019–1041,1079–1084`. Convolution with the actual radial
dyadic kernels gives local weak Poisson bands. The normalization here is the
Laplacian; the paper's operator `Δ/2` requires twice this kernel.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace EinsteinRelation.Correctors

open Entropy (continuous_euclideanNorm')

variable {d : ℕ}

/-- Subtraction of spatial kernels commutes almost surely with convolution
of an integrable stationary field (`paper/main.tex:1019–1025`). -/
theorem horizontalMollify_sub_kernel_ae {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) {K L : Vec d → ℝ}
    (hK : Measurable K) (hKi : Integrable K volume)
    (hL : Measurable L) (hLi : Integrable L volume)
    {f : FieldPair d → ℝ} (hf : Measurable f) (hfi : Integrable f Q) :
    horizontalMollify (fun z => K z - L z) f =ᵐ[Q]
      fun ω => horizontalMollify K f ω - horizontalMollify L f ω := by
  filter_upwards [ae_integrable_kernel_translate hQ hK hKi hf hfi,
    ae_integrable_kernel_translate hQ hL hLi hf hfi] with ω hKω hLω
  simp only [horizontalMollify, sub_mul]
  exact integral_sub hKω hLω

namespace KernelCalculus

/-- Spatial differentiation does not enlarge the topological support
(`paper/main.tex:1079–1084`). -/
theorem tsupport_coordinateIterate_subset (K : Vec d → ℝ) (cs : List (Fin d)) :
    tsupport (coordinateIterate cs K) ⊆ tsupport K := by
  induction cs with
  | nil => exact Set.Subset.rfl
  | cons i cs ih =>
    have hstep : tsupport (coordinateDerivative i (coordinateIterate cs K)) ⊆
        tsupport (coordinateIterate cs K) := by
      apply closure_minimal _ isClosed_closure
      intro x hx
      by_contra hn
      apply hx
      simp only [coordinateDerivative, fderiv_of_notMem_tsupport ℝ hn,
        ContinuousLinearMap.zero_apply]
    exact hstep.trans ih

/-- Every derivative of a kernel vanishing beyond radius `ρ` is supported
in the corresponding closed Euclidean ball (`paper/main.tex:1079–1084`). -/
theorem support_coordinateIterate_subset_ball {K : Vec d → ℝ} {ρ : ℝ}
    (hzero : ∀ x, ρ ≤ euclideanNorm x → K x = 0) (cs : List (Fin d)) :
    Function.support (coordinateIterate cs K) ⊆ {x | euclideanNorm x ≤ ρ} := by
  have hbase : Function.support K ⊆ {x | euclideanNorm x ≤ ρ} := by
    intro x hx
    change euclideanNorm x ≤ ρ
    by_contra! hgt
    exact hx (hzero x hgt.le)
  exact subset_closure.trans ((tsupport_coordinateIterate_subset K cs).trans
    (closure_minimal hbase (isClosed_le continuous_euclideanNorm' continuous_const)))

end KernelCalculus

/-- All spatial derivatives of compact-kernel convolutions retain a
precise Euclidean observation window (`paper/main.tex:1079–1084`). -/
theorem measurable_localSigma_coordinateIterate_convolution {K : Vec d → ℝ}
    (hK : ContDiff ℝ (⊤ : ℕ∞) K) {ρ L : ℝ}
    (hzero : ∀ x, ρ ≤ euclideanNorm x → K x = 0)
    {f : FieldPair d → ℝ}
    (hf : Measurable[localSigma {x : Vec d | euclideanNorm x < L}] f)
    (cs : List (Fin d)) :
    Measurable[localSigma {x : Vec d | euclideanNorm x < L + ρ}]
      (horizontalMollify (coordinateIterate cs K) f) := by
  refine measurable_localSigma_horizontalMollify
    (measurableSet_le continuous_euclideanNorm'.measurable measurable_const)
    (fun x hx y hy => ?_)
    (KernelCalculus.contDiff_coordinateIterate hK cs).continuous.measurable
    (KernelCalculus.support_coordinateIterate_subset_ball hzero cs) hf
  have ht := TimeChange.euclideanNorm_add_le x y
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  linarith

/-- The actual radial dyadic convolution solves its weak Poisson equation
(`paper/main.tex:1019–1025`). -/
theorem hasWeakHorizontalDivergence_radialBand {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) (hd : 2 ≤ d)
    {r : ℝ} (hr : 0 < r) {f : FieldPair d → ℝ}
    (hf : Measurable f) (hf2 : MemLp f 2 Q) :
    HasWeakHorizontalDivergence Q hQ (kernelGradient (radialBandKernel d r) f)
      (fun ω => horizontalMollify (radialAverage d r) f ω -
        horizontalMollify (radialAverage d (2 * r)) f ω) := by
  have h := hasWeakHorizontalDivergence_kernelGradient hQ
    (radialBandKernel_contDiff hd hr) (radialBandKernel_hasCompactSupport hd hr) hf hf2
  refine Entropy.HasWeakHorizontalDivergence.congr_div h ?_
  have hfun : coordLaplacian (radialBandKernel d r) =
      fun x => radialAverage d r x - radialAverage d (2 * r) x :=
    funext (coordLaplacian_radialBandKernel hd hr)
  rw [hfun]
  have h2r : 0 < 2 * r := mul_pos (by norm_num) hr
  exact horizontalMollify_sub_kernel_ae hQ (radialAverage_contDiff hr).continuous.measurable
    ((radialAverage_contDiff hr).continuous.integrable_of_hasCompactSupport
      (radialAverage_hasCompactSupport hr))
    (radialAverage_contDiff h2r).continuous.measurable
    ((radialAverage_contDiff h2r).continuous.integrable_of_hasCompactSupport
      (radialAverage_hasCompactSupport h2r)) hf (hf2.integrable one_le_two)

/-- Every derivative of a radial dyadic band is observed in a ball whose
radius grows by `2r` (`paper/main.tex:1079–1084`). -/
theorem measurable_localSigma_radialBand_derivative (hd : 2 ≤ d)
    {r L : ℝ} (hr : 0 < r) {f : FieldPair d → ℝ}
    (hf : Measurable[localSigma {x : Vec d | euclideanNorm x < L}] f)
    (cs : List (Fin d)) :
    Measurable[localSigma {x : Vec d | euclideanNorm x < L + 2 * r}]
      (horizontalMollify (coordinateIterate cs (radialBandKernel d r)) f) :=
  measurable_localSigma_coordinateIterate_convolution (radialBandKernel_contDiff hd hr)
    (fun _ hx => radialBandKernel_tail hd hr hx) hf cs

/-- The exact `L¹` kernel scaling controls every stationary derivative
convolution (`paper/main.tex:1015–1018,1028–1035`). The heat-transfer argument
is needed in addition to gain one power of the scale. -/
theorem eLpNorm_radialBand_derivative_le {Q : Measure (FieldPair d)} [SFinite Q]
    (hQ : IsStationary Q) (hd : 2 ≤ d) (cs : List (Fin d)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → ∀ p : ℝ≥0∞, 1 ≤ p → p ≠ ∞ →
      ∀ f : FieldPair d → ℝ, Measurable f →
      eLpNorm (horizontalMollify (coordinateIterate cs (radialBandKernel d r)) f) p Q ≤
        ENNReal.ofReal (C * (r ^ 2 / r ^ cs.length)) * eLpNorm f p Q := by
  obtain ⟨C, hC, hbound⟩ := radialBandKernel_derivative_bounds hd cs
  refine ⟨C, hC, fun r hr p hp hpt f hf => ?_⟩
  have h := eLpNorm_horizontalMollify_le hQ hp hpt
    (KernelCalculus.contDiff_coordinateIterate (radialBandKernel_contDiff hd hr) cs).continuous.measurable
    (hbound r hr).1 hf
  rwa [(hbound r hr).2] at h

/-- The radial averaging sources telescope exactly at the dyadic scales
(`paper/main.tex:1019–1025`). -/
theorem sum_radialBand_sources (N : ℕ) (f : FieldPair d → ℝ) (ω : FieldPair d) :
    (∑ k ∈ Finset.range N,
      (horizontalMollify (radialAverage d ((2 : ℝ) ^ k)) f ω -
        horizontalMollify (radialAverage d (2 * (2 : ℝ) ^ k)) f ω)) =
      horizontalMollify (radialAverage d 1) f ω -
        horizontalMollify (radialAverage d ((2 : ℝ) ^ N)) f ω := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    rw [mul_comm ((2 : ℝ) ^ N) 2]
    ring

/-- Summing the constructed radial band gradients gives the telescoped
weak Poisson equation (`paper/main.tex:1019–1025`). -/
theorem hasWeakHorizontalDivergence_sum_radialBands {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) (hd : 2 ≤ d)
    (N : ℕ) {f : FieldPair d → ℝ} (hf : Measurable f) (hf2 : MemLp f 2 Q) :
    HasWeakHorizontalDivergence Q hQ
      (fun ω => ∑ k ∈ Finset.range N, kernelGradient (radialBandKernel d ((2 : ℝ) ^ k)) f ω)
      (fun ω => horizontalMollify (radialAverage d 1) f ω -
        horizontalMollify (radialAverage d ((2 : ℝ) ^ N)) f ω) := by
  have h := HasWeakHorizontalDivergence.finset_sum (Finset.range N)
    (fun k _ => hasWeakHorizontalDivergence_radialBand hQ hd (by positivity : 0 < (2 : ℝ) ^ k)
      hf hf2)
  exact Entropy.HasWeakHorizontalDivergence.congr_div h
    (ae_of_all _ fun ω => sum_radialBand_sources N f ω)

end EinsteinRelation.Correctors
