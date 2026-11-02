import EinsteinFull.Calculus.S2SmoothingOperator
import EinsteinFull.Frozen.GaussianAveragingSeminorm

/-!
# Unforced Gaussian averages are controlled by the isotropic averaging seminorm

For `ε u ≥ 2` and a field `F` with `gaussianAveragingSeminorm F ≤ C`, the unforced Gaussian
average and its first derivative average of `F j` are bounded by `C ρ^{-d/2}` and
`√(2 K u) u⁻¹ C ρ^{-d/2}` respectively, with `ρ² = ε u / 2`.
-/

open MeasureTheory

namespace EinsteinFull

open EinsteinRelation

variable {d : ℕ} {Λ₀ r₀ : ℝ}

theorem integral_norm_deconvKernel (Q : EnvironmentLaw d Λ₀ r₀) {u : ℝ} (hu : 0 < u) :
    (∫ x : Vec d, ‖deconvKernel Q u x‖) = 1 := by
  have hn : ∀ y : Vec d, 0 ≤ anisotropicGaussian (deconvMat Q) u y :=
    fun y => anisotropicGaussian_nonneg _ hu y
  unfold deconvKernel
  simp_rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hn _)]
  exact integral_anisotropicGaussian _ (posDef_deconvMat Q) u hu

theorem integral_norm_deconvDerivKernel_le (Q : EnvironmentLaw d Λ₀ r₀) {u : ℝ} (hu : 0 < u)
    (j : Fin d) :
    (∫ x : Vec d, ‖deconvDerivKernel Q u j x‖) ≤
      Real.sqrt (2 * sourceReducedBound Λ₀ * u) / u := by
  have hn : ∀ y : Vec d, 0 ≤ anisotropicGaussian (deconvMat Q) u y :=
    fun y => anisotropicGaussian_nonneg _ hu y
  have hnorm : ∀ x : Vec d, ‖deconvDerivKernel Q u j x‖ =
      |((deconvMat Q)⁻¹.mulVec x) j| * anisotropicGaussian (deconvMat Q) u x / u := by
    intro x
    unfold deconvDerivKernel
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg (hn x),
      abs_of_pos hu]
  simp_rw [hnorm]
  rw [integral_div]
  exact div_le_div_of_nonneg_right (deconv_linear_L1_le Q j hu) hu.le

theorem norm_gaussianAverage_le_iso (hd : 2 ≤ d) (Q : EnvironmentLaw d Λ₀ r₀) {u : ℝ}
    (hu : 0 < u) (f : Lp ℂ 2 (reducedLaw Q)) :
    ‖gaussianAverage hd Q u hu f‖ ≤
      ‖kernelAvg (reducedLaw Q) (reducedLaw_stationary Q) (isoKernel Q u) f‖ := by
  haveI := reducedLaw_probability Q
  have h : gaussianAverage hd Q u hu f = kernelAvg (reducedLaw Q) (reducedLaw_stationary Q)
      (deconvKernel Q u) (kernelAvg (reducedLaw Q) (reducedLaw_stationary Q)
        (isoKernel Q u) f) := by
    rw [kernelAvg_conv _ _ _ _ (deconvKernel_integrable Q hu) (isoKernel_integrable Q hu)
      (deconvKernel_continuous Q u) (isoKernel_continuous Q u), kernelConv_deconv Q hu,
      gaussianAverage_eq_kernelAvg]
  rw [h]
  calc _ ≤ (∫ x : Vec d, ‖deconvKernel Q u x‖) *
        ‖kernelAvg (reducedLaw Q) (reducedLaw_stationary Q) (isoKernel Q u) f‖ :=
      norm_kernelAvg_le _ _ _ _
    _ = _ := by rw [integral_norm_deconvKernel Q hu, one_mul]

theorem norm_gaussianDerivativeAverage_le_iso (hd : 2 ≤ d) (Q : EnvironmentLaw d Λ₀ r₀)
    {u : ℝ} (hu : 0 < u) (dirs : Fin 1 → Fin d) (f : Lp ℂ 2 (reducedLaw Q)) :
    ‖gaussianDerivativeAverage hd Q u hu 1 dirs f‖ ≤
      Real.sqrt (2 * sourceReducedBound Λ₀ * u) / u *
        ‖kernelAvg (reducedLaw Q) (reducedLaw_stationary Q) (isoKernel Q u) f‖ := by
  haveI := reducedLaw_probability Q
  have h : gaussianDerivativeAverage hd Q u hu 1 dirs f =
      kernelAvg (reducedLaw Q) (reducedLaw_stationary Q) (deconvDerivKernel Q u (dirs 0))
        (kernelAvg (reducedLaw Q) (reducedLaw_stationary Q) (isoKernel Q u) f) := by
    rw [kernelAvg_conv _ _ _ _ (deconvDerivKernel_integrable Q hu (dirs 0))
      (isoKernel_integrable Q hu) (deconvDerivKernel_continuous Q u (dirs 0))
      (isoKernel_continuous Q u), kernelConv_deconvDeriv Q hu,
      gaussianDerivativeAverage_eq_kernelAvg]
  rw [h]
  calc _ ≤ (∫ x : Vec d, ‖deconvDerivKernel Q u (dirs 0) x‖) *
        ‖kernelAvg (reducedLaw Q) (reducedLaw_stationary Q) (isoKernel Q u) f‖ :=
      norm_kernelAvg_le _ _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right (integral_norm_deconvDerivKernel_le Q hu (dirs 0))
        (norm_nonneg _)

theorem euclideanHeatKernel_eq_aniso (t : ℝ) (x : Vec d) :
    Correctors.euclideanHeatKernel t x = anisotropicGaussian (1 : Mat d) (2 * t) x := by
  unfold Correctors.euclideanHeatKernel anisotropicGaussian
  rw [quad_eq_dot, inv_one, Matrix.one_mulVec, Matrix.det_one, Real.sqrt_one, div_one,
    show 2 * Real.pi * (2 * t) = 4 * Real.pi * t by ring,
    show 2 * (2 * t) = 4 * t by ring]
  rfl

theorem kernelAvg_iso_eq (Q : EnvironmentLaw d Λ₀ r₀) (u : ℝ) (f : Lp ℂ 2 (reducedLaw Q)) :
    kernelAvg (reducedLaw Q) (reducedLaw_stationary Q) (isoKernel Q u) f =
      ∫ x : Vec d, (Correctors.euclideanHeatKernel (deconvEps Λ₀ * u / 2) x : ℂ) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f := by
  unfold kernelAvg isoKernel
  simp_rw [euclideanHeatKernel_eq_aniso, show 2 * (deconvEps Λ₀ * u / 2) = deconvEps Λ₀ * u by
    ring]

theorem iso_term_le (hd : 2 ≤ d) (Q : EnvironmentLaw d Λ₀ r₀) {u : ℝ}
    (hεu : 2 ≤ deconvEps Λ₀ * u) (F : Fin d → Lp ℂ 2 (reducedLaw Q)) {C : ℝ} (hC : 0 ≤ C)
    (hsem : gaussianAveragingSeminorm hd Q F ≤ ENNReal.ofReal C) (j : Fin d) :
    Real.sqrt (deconvEps Λ₀ * u / 2) ^ ((d : ℝ) / 2) *
      ‖kernelAvg (reducedLaw Q) (reducedLaw_stationary Q) (isoKernel Q u) (F j)‖ ≤ C := by
  have hnn : 0 ≤ deconvEps Λ₀ * u / 2 := by linarith
  have hρ : 1 ≤ Real.sqrt (deconvEps Λ₀ * u / 2) := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by linarith)
  simp only [gaussianAveragingSeminorm, iSup_le_iff, ENNReal.ofReal_le_ofReal_iff hC] at hsem
  have h := hsem _ hρ
  simp_rw [Real.sq_sqrt hnn] at h
  simp_rw [← kernelAvg_iso_eq Q u] at h
  have hj : ‖kernelAvg (reducedLaw Q) (reducedLaw_stationary Q) (isoKernel Q u) (F j)‖ ≤
      Real.sqrt (∑ i : Fin d, ‖kernelAvg (reducedLaw Q) (reducedLaw_stationary Q)
        (isoKernel Q u) (F i)‖ ^ 2) := by
    calc _ = Real.sqrt (‖kernelAvg (reducedLaw Q) (reducedLaw_stationary Q)
          (isoKernel Q u) (F j)‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ _ := Real.sqrt_le_sqrt (Finset.single_le_sum
          (f := fun i => ‖kernelAvg (reducedLaw Q) (reducedLaw_stationary Q)
            (isoKernel Q u) (F i)‖ ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j))
  exact (mul_le_mul_of_nonneg_left hj (Real.rpow_nonneg (Real.sqrt_nonneg _) _)).trans h

end EinsteinFull
