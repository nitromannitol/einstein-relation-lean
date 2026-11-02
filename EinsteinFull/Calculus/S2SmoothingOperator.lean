import EinsteinFull.Calculus.S2KernelAverage
import EinsteinFull.Calculus.S2DeconvMatrix
import EinsteinFull.Frozen.GaussianAverage
import EinsteinFull.Frozen.GaussianDerivativeAverage
import EinsteinFull.Frozen.ReducedLawProbability

/-!
# Isotropic smoothing of the unforced Gaussian averages

The unforced Gaussian average and its first derivative average factor through the isotropic
heat average of variance `ε u`, up to an operator of `L¹` norm one, respectively
`≤ √(2 K u) / u`.
-/

open MeasureTheory

namespace EinsteinFull

open EinsteinRelation

variable {d : ℕ} {Λ₀ r₀ : ℝ}

theorem continuous_anisotropicGaussian' (A : Mat d) (s : ℝ) :
    Continuous (anisotropicGaussian A s) :=
  (contDiff_anisotropicGaussian A s).continuous

theorem continuous_mulVec_coord (M : Mat d) (j : Fin d) :
    Continuous fun x : Vec d => (M.mulVec x) j := by
  simp only [Matrix.mulVec, dotProduct]
  fun_prop

theorem posDef_one' : (1 : Mat d).PosDef := Matrix.PosDef.one

/-- Isotropic kernel with covariance `ε u I`. -/
noncomputable def isoKernel (Q : EnvironmentLaw d Λ₀ r₀) (u : ℝ) : Vec d → ℂ :=
  fun x => ((anisotropicGaussian (1 : Mat d) (deconvEps Λ₀ * u) x : ℝ) : ℂ)

/-- The remainder density with covariance `u (ā - ε I)`. -/
noncomputable def deconvKernel (Q : EnvironmentLaw d Λ₀ r₀) (u : ℝ) : Vec d → ℂ :=
  fun x => ((anisotropicGaussian (deconvMat Q) u x : ℝ) : ℂ)

/-- Its first derivative kernel `(A'⁻¹ x)_j g(x) / u`. -/
noncomputable def deconvDerivKernel (Q : EnvironmentLaw d Λ₀ r₀) (u : ℝ) (j : Fin d) :
    Vec d → ℂ :=
  fun x => (((deconvMat Q)⁻¹.mulVec x j * anisotropicGaussian (deconvMat Q) u x / u : ℝ) : ℂ)

theorem isoKernel_integrable (Q : EnvironmentLaw d Λ₀ r₀) {u : ℝ} (hu : 0 < u) :
    Integrable (isoKernel Q u) :=
  (integrable_anisotropicGaussian (1 : Mat d) posDef_one' _
    (mul_pos (deconvEps_pos Q) hu)).ofReal

theorem isoKernel_continuous (Q : EnvironmentLaw d Λ₀ r₀) (u : ℝ) :
    Continuous (isoKernel Q u) :=
  Complex.continuous_ofReal.comp (continuous_anisotropicGaussian' _ _)

theorem deconvKernel_integrable (Q : EnvironmentLaw d Λ₀ r₀) {u : ℝ} (hu : 0 < u) :
    Integrable (deconvKernel Q u) :=
  (integrable_anisotropicGaussian (deconvMat Q) (posDef_deconvMat Q) u hu).ofReal

theorem deconvKernel_continuous (Q : EnvironmentLaw d Λ₀ r₀) (u : ℝ) :
    Continuous (deconvKernel Q u) :=
  Complex.continuous_ofReal.comp (continuous_anisotropicGaussian' _ _)

theorem deconvDerivKernel_integrable (Q : EnvironmentLaw d Λ₀ r₀) {u : ℝ} (hu : 0 < u)
    (j : Fin d) : Integrable (deconvDerivKernel Q u j) :=
  ((integrable_mulVec_mul_anisotropicGaussian (deconvMat Q) (posDef_deconvMat Q)
    (deconvMat Q)⁻¹ j u hu).div_const u).ofReal

theorem deconvDerivKernel_continuous (Q : EnvironmentLaw d Λ₀ r₀) (u : ℝ) (j : Fin d) :
    Continuous (deconvDerivKernel Q u j) :=
  Complex.continuous_ofReal.comp
    (((continuous_mulVec_coord _ j).mul (continuous_anisotropicGaussian' _ _)).div_const u)

/-- The reflected-variable form of the isotropic convolution. -/
theorem integral_flip_isotropic (Q : EnvironmentLaw d Λ₀ r₀) (u : ℝ) (x : Vec d)
    (h : Vec d → ℝ) :
    (∫ y : Vec d, h (x - y) * anisotropicGaussian (1 : Mat d) (deconvEps Λ₀ * u) y) =
      ∫ y : Vec d, anisotropicGaussian (1 : Mat d) (deconvEps Λ₀ * u) (x - y) * h y := by
  have hs := integral_sub_left_eq_self (μ := (volume : Measure (Vec d)))
    (fun y : Vec d => anisotropicGaussian (1 : Mat d) (deconvEps Λ₀ * u) (x - y) * h y) x
  simp only [sub_sub_cancel] at hs
  rw [← hs]
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => mul_comm _ _)

theorem kernelConv_deconv (Q : EnvironmentLaw d Λ₀ r₀) {u : ℝ} (hu : 0 < u) :
    kernelConv (deconvKernel Q u) (isoKernel Q u) =
      fun x => ((anisotropicGaussian (homogenizedCoefficient Q) u x : ℝ) : ℂ) := by
  funext x
  unfold kernelConv deconvKernel isoKernel
  simp_rw [← Complex.ofReal_mul]
  rw [integral_complex_ofReal]
  congr 1
  rw [integral_flip_isotropic Q u x (anisotropicGaussian (deconvMat Q) u),
    integral_isotropic_mul_gaussian (posDef_deconvMat Q) (deconvEps_pos Q) hu x,
    gaussSumMat_deconvMat]

theorem kernelConv_deconvDeriv (Q : EnvironmentLaw d Λ₀ r₀) {u : ℝ} (hu : 0 < u) (j : Fin d) :
    kernelConv (deconvDerivKernel Q u j) (isoKernel Q u) =
      fun x => (((homogenizedCoefficient Q)⁻¹.mulVec x j *
        anisotropicGaussian (homogenizedCoefficient Q) u x / u : ℝ) : ℂ) := by
  funext x
  unfold kernelConv deconvDerivKernel isoKernel
  simp_rw [← Complex.ofReal_mul]
  rw [integral_complex_ofReal]
  congr 1
  rw [integral_flip_isotropic Q u x (fun y => (deconvMat Q)⁻¹.mulVec y j *
    anisotropicGaussian (deconvMat Q) u y / u)]
  have h := integral_linear_isotropic_mul_gaussian (posDef_deconvMat Q) (deconvEps_pos Q) hu j x
  rw [gaussSumMat_deconvMat] at h
  have e : ∀ y : Vec d, anisotropicGaussian (1 : Mat d) (deconvEps Λ₀ * u) (x - y) *
      ((deconvMat Q)⁻¹.mulVec y j * anisotropicGaussian (deconvMat Q) u y / u) =
      ((deconvMat Q)⁻¹.mulVec y j * (anisotropicGaussian (1 : Mat d) (deconvEps Λ₀ * u) (x - y) *
        anisotropicGaussian (deconvMat Q) u y)) / u := by
    intro y
    ring
  simp_rw [e]
  rw [integral_div, h]

theorem gaussianAverage_eq_kernelAvg (hd : 2 ≤ d) (Q : EnvironmentLaw d Λ₀ r₀) {u : ℝ}
    (hu : 0 < u) (f : Lp ℂ 2 (reducedLaw Q)) :
    gaussianAverage hd Q u hu f = kernelAvg (reducedLaw Q) (reducedLaw_stationary Q)
      (fun x => ((anisotropicGaussian (homogenizedCoefficient Q) u x : ℝ) : ℂ)) f := by
  unfold gaussianAverage kernelAvg
  simp only [homogenizedGaussianKernel_zero_eq_ofReal]

theorem gaussianDerivativeAverage_eq_kernelAvg (hd : 2 ≤ d) (Q : EnvironmentLaw d Λ₀ r₀)
    {u : ℝ} (hu : 0 < u) (dirs : Fin 1 → Fin d) (f : Lp ℂ 2 (reducedLaw Q)) :
    gaussianDerivativeAverage hd Q u hu 1 dirs f = kernelAvg (reducedLaw Q)
      (reducedLaw_stationary Q) (fun x => (((homogenizedCoefficient Q)⁻¹.mulVec x (dirs 0) *
        anisotropicGaussian (homogenizedCoefficient Q) u x / u : ℝ) : ℂ)) f := by
  unfold gaussianDerivativeAverage kernelAvg
  have key : ∀ x : Vec d, iteratedFDeriv ℝ 1
      (homogenizedGaussianKernel Q ⟨0, by omega⟩ u hu 0) (-x)
      (fun j => unitVector (dirs j)) =
      (((homogenizedCoefficient Q)⁻¹.mulVec x (dirs 0) *
        anisotropicGaussian (homogenizedCoefficient Q) u x / u : ℝ) : ℂ) := by
    intro x
    rw [iteratedFDeriv_one_apply]
    try beta_reduce
    rw [fderiv_homogenizedGaussianKernel_zero_coordinate, homogenizedGaussianKernel_zero_eq_ofReal,
      ← Complex.ofReal_mul, anisotropicGaussian_neg, Matrix.mulVec_neg]
    congr 1
    simp only [Pi.neg_apply]
    ring
  simp_rw [key]

end EinsteinFull
