import EinsteinRelation.Correctors.StationaryKernelConvolution
import EinsteinRelation.Correctors.HeatKernelConvolutionIntegrability
import EinsteinRelation.Calculus.Generator
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! Source: `paper/main.tex:732-748`. Linearity, means and translation of the literal
horizontal convolutions of integrable stationary observables. Useful existing tools:
`ae_integrable_kernel_translate`, `integrable_stationary_weight`,
`horizontalMollify_sub_kernel_ae`, `Probability.integral_translate`. -/
open MeasureTheory Filter Topology
namespace EinsteinRelation.Correctors

/-- Convolution is almost surely additive in the observable. -/
theorem horizontalMollify_sub_ae {d : ℕ} {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) {K : Vec d → ℝ}
    (hK : Measurable K) (hKi : Integrable K volume)
    {f g : FieldPair d → ℝ} (hf : Measurable f) (hfi : Integrable f Q)
    (hg : Measurable g) (hgi : Integrable g Q) :
    horizontalMollify K (fun ω => f ω - g ω) =ᵐ[Q]
      fun ω => horizontalMollify K f ω - horizontalMollify K g ω := by
  filter_upwards [ae_integrable_kernel_translate hQ hK hKi hf hfi,
    ae_integrable_kernel_translate hQ hK hKi hg hgi] with ω hfω hgω
  simp only [horizontalMollify, mul_sub]
  exact integral_sub hfω hgω

/-- Convolution of a finite sum of kernels is almost surely the sum of convolutions. -/
theorem horizontalMollify_sum_kernel_ae {d : ℕ} {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) {ι : Type*} (s : Finset ι)
    {K : ι → Vec d → ℝ} (hK : ∀ i, Measurable (K i)) (hKi : ∀ i, Integrable (K i) volume)
    {f : FieldPair d → ℝ} (hf : Measurable f) (hfi : Integrable f Q) :
    horizontalMollify (fun x => ∑ i ∈ s, K i x) f =ᵐ[Q]
      fun ω => ∑ i ∈ s, horizontalMollify (K i) f ω := by
  have hae : ∀ᵐ ω ∂Q, ∀ i ∈ s, Integrable (fun z => K i z * f (translate z ω)) volume :=
    (Filter.eventually_all_finset s).mpr fun i _ =>
      ae_integrable_kernel_translate hQ (hK i) (hKi i) hf hfi
  filter_upwards [hae] with ω hω
  simp only [horizontalMollify, Finset.sum_mul]
  exact integral_finset_sum s hω

/-- Translating the observable translates the kernel, exactly. -/
theorem horizontalMollify_comp_translate {d : ℕ} (K : Vec d → ℝ)
    (f : FieldPair d → ℝ) (z : Vec d) (ω : FieldPair d) :
    horizontalMollify K (fun ρ => f (translate z ρ)) ω =
      horizontalMollify (fun x => K (x - z)) f ω := by
  unfold horizontalMollify
  simp only [translate_add]
  have h := integral_add_right_eq_self (μ := (volume : Measure (Vec d)))
    (fun x : Vec d => K (x - z) * f (translate x ω)) z
  simp only [add_sub_cancel_right] at h
  rw [← h]
  congr 1
  funext x
  rw [add_comm z x]

/-- The mean of a convolution is the kernel mass times the mean. -/
theorem integral_horizontalMollify_of_integrable {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) {K : Vec d → ℝ}
    (hK : Measurable K) (hKi : Integrable K volume)
    {f : FieldPair d → ℝ} (hf : Measurable f) (hfi : Integrable f Q) :
    ∫ ω, horizontalMollify K f ω ∂Q = (∫ x, K x) * ∫ ω, f ω ∂Q := by
  have hint := integrable_kernel_translate hQ hK hKi hf hfi
  change (∫ ω, (∫ x : Vec d, K x * f (translate x ω)) ∂Q) = _
  rw [integral_integral_swap hint]
  simp_rw [integral_const_mul, Probability.integral_translate Q hQ _ f hf]
  exact integral_mul_const _ _

/-- Heat smoothing preserves the mean of an integrable stationary observable. -/
theorem integral_heatSmoothed {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {f : FieldPair d → ℝ} (hf : Measurable f) (hfi : Integrable f Q) (t : ℝ) (ht : 0 ≤ t) :
    ∫ ω, heatSmoothed t f ω ∂Q = ∫ ω, f ω ∂Q := by
  rcases ht.eq_or_lt with rfl | htpos
  · simp [heatSmoothed]
  · have hfun : heatSmoothed t f = horizontalMollify (euclideanHeatKernel t) f := by
      funext ω
      simp [heatSmoothed, horizontalMollify, htpos.ne']
    rw [hfun, integral_horizontalMollify_of_integrable Q hQ
      (continuous_euclideanHeatKernel t).measurable (integrable_euclideanHeatKernel htpos) hf hfi,
      integral_euclideanHeatKernel htpos, one_mul]

end EinsteinRelation.Correctors

/-! Source: `paper/main.tex:732-748`. Mixed coordinate derivatives of smooth spatial
tests commute (`ContDiffAt.isSymmSndFDerivAt`; a private version is in
`Calculus/ClosedPotentialOrbitCurlSupport.lean`). -/
open MeasureTheory
namespace EinsteinRelation.Correctors

theorem coordinateDerivative_comm {d : ℕ} {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (i j : Fin d) :
    coordinateDerivative i (coordinateDerivative j ψ) =
      coordinateDerivative j (coordinateDerivative i ψ) := by
  ext x
  have hinner : (2 : ℕ∞) ≤ (⊤ : ℕ∞) := le_top
  have hn : minSmoothness ℝ 2 ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact_mod_cast hinner
  have hs := (hψ.contDiffAt (x := x)).isSymmSndFDerivAt hn
  have hd : DifferentiableAt ℝ (fun y => fderiv ℝ ψ y) x := by
    have hbound : (1 : WithTop ℕ∞) + 1 ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) := by
      change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
      exact_mod_cast hinner
    exact ((hψ.contDiffAt (x := x)).fderiv_right hbound).differentiableAt (by norm_num)
  have happly (v w : Vec d) :
      fderiv ℝ (fun y => fderiv ℝ ψ y v) x w =
        (fderiv ℝ (fderiv ℝ ψ) x w) v := by
    have h := fderiv_clm_apply hd (differentiableAt_const (x := x) v)
    have h' := congrArg (fun L : Vec d →L[ℝ] ℝ => L w) h
    simpa using h'
  have hswap := hs.iteratedFDeriv_cons (v := unitVector i) (w := unitVector j)
  change fderiv ℝ (coordinateDerivative j ψ) x (unitVector i) =
    fderiv ℝ (coordinateDerivative i ψ) x (unitVector j)
  rw [show coordinateDerivative j ψ = fun y => fderiv ℝ ψ y (unitVector j) by rfl,
      show coordinateDerivative i ψ = fun y => fderiv ℝ ψ y (unitVector i) by rfl]
  rw [happly (unitVector j) (unitVector i), happly (unitVector i) (unitVector j)]
  simpa [iteratedFDeriv_two_apply] using hswap

end EinsteinRelation.Correctors
