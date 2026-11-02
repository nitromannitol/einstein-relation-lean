import EinsteinFull.Work.W3.GaussianConvolutionSupport

/-! Exact parabolic scaling of the actual anisotropic complex-force kernel. -/

namespace EinsteinFull

open EinsteinRelation
open scoped BigOperators

variable {d : ℕ} {Λ₀ r₀ : ℝ}

/-- Spatial dilation keeps the full covariance matrix and determinant. -/
theorem anisotropicGaussian_parabolic_scale (A : Mat d) (R s : ℝ)
    (hR : 0 < R) (hs : 0 < s) (x : Vec d) :
    anisotropicGaussian A (R ^ 2 * s) x =
      R ^ (-(d : ℝ)) * anisotropicGaussian A s (R⁻¹ • x) := by
  have hq : (∑ j, ∑ k, (R⁻¹ • x) j * (A⁻¹) j k * (R⁻¹ • x) k) =
      R⁻¹ ^ 2 * (∑ j, ∑ k, x j * (A⁻¹) j k * x k) := by
    simp only [Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hp : (R ^ 2) ^ (-(d : ℝ) / 2) = R ^ (-(d : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hR.le]
    congr 1
    ring
  have hn : 2 * Real.pi * (R ^ 2 * s) = (2 * Real.pi * s) * R ^ 2 := by ring
  unfold anisotropicGaussian
  rw [hq, hn, Real.mul_rpow (mul_pos (mul_pos (by norm_num) Real.pi_pos) hs).le
    (sq_nonneg R), hp]
  have he (q : ℝ) : -(R⁻¹ ^ 2 * q) / (2 * s) = -q / (2 * (R ^ 2 * s)) := by
    field_simp
  rw [he]
  ring

/-- Parabolic scaling of the literal complex kernel, with scaled force `ζ R`. -/
theorem homogenizedGaussianKernel_parabolic_scale (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) (R s : ℝ) (hR : 0 < R) (hs : 0 < s) (ζ : ℂ) (x : Vec d) :
    homogenizedGaussianKernel Q i (R ^ 2 * s) (mul_pos (sq_pos_of_pos hR) hs) ζ x =
      (R ^ (-(d : ℝ)) : ℝ) •
        homogenizedGaussianKernel Q i s hs (ζ * (R : ℂ)) (R⁻¹ • x) := by
  rw [homogenizedGaussianKernel_eq_exp_tilt, homogenizedGaussianKernel_eq_exp_tilt,
    anisotropicGaussian_parabolic_scale _ R s hR hs]
  simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.real_smul,
    Pi.smul_apply, smul_eq_mul, Complex.ofReal_inv]
  have he : ζ * (x i : ℂ) - ζ ^ 2 * ((R : ℂ) ^ 2 * (s : ℂ)) *
      (homogenizedCoefficient Q i i : ℂ) / 2 =
      (ζ * (R : ℂ)) * ((R : ℂ)⁻¹ * (x i : ℂ)) -
        (ζ * (R : ℂ)) ^ 2 * (s : ℂ) * (homogenizedCoefficient Q i i : ℂ) / 2 := by
    field_simp [Complex.ofReal_ne_zero.mpr hR.ne']
  rw [he]
  ring

/-- The first derivative has the additional inverse spatial scale. -/
theorem fderiv_homogenizedGaussianKernel_parabolic_scale (Q : EnvironmentLaw d Λ₀ r₀)
    (i j : Fin d) (R s : ℝ) (hR : 0 < R) (hs : 0 < s) (ζ : ℂ) (x : Vec d) :
    fderiv ℝ (homogenizedGaussianKernel Q i (R ^ 2 * s)
      (mul_pos (sq_pos_of_pos hR) hs) ζ) x (unitVector j) =
      ((R ^ (-(d : ℝ)) / R : ℝ) : ℂ) *
        fderiv ℝ (homogenizedGaussianKernel Q i s hs (ζ * (R : ℂ)))
          (R⁻¹ • x) (unitVector j) := by
  rw [fderiv_homogenizedGaussianKernel_complexForce_coordinate,
    fderiv_homogenizedGaussianKernel_complexForce_coordinate,
    homogenizedGaussianKernel_parabolic_scale Q i R s hR hs]
  simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul,
    Complex.ofReal_inv, Complex.ofReal_div, Complex.ofReal_pow, Complex.real_smul]
  field_simp [Complex.ofReal_ne_zero.mpr hR.ne', Complex.ofReal_ne_zero.mpr hs.ne']

end EinsteinFull
