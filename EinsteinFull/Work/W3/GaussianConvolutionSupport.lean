import EinsteinFull.Work.W3.ComplexGaussianProfileSupport
import Mathlib.Analysis.Matrix.Order
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Lebesgue Gaussian convolution on the coordinate carrier

All integrals use the existing `Vec d = Fin d → ℝ` with product Lebesgue
measure. Matrix square roots only implement a change of variables; the
source-facing density retains its determinant, inverse and covariance `s A`.
-/

namespace EinsteinFull

open EinsteinRelation MeasureTheory
open scoped BigOperators MatrixOrder

variable {d : ℕ}

private noncomputable def matrixMeasurableEquiv (B : Mat d) (hB : B.det ≠ 0) :
    Vec d ≃ᵐ Vec d :=
  (Matrix.toLinearEquiv' B
    ((Matrix.isUnit_iff_isUnit_det B).mpr (isUnit_iff_ne_zero.mpr hB)).invertible
      ).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv

private lemma matrixMeasurableEquiv_apply (B : Mat d) (hB : B.det ≠ 0) (x : Vec d) :
    matrixMeasurableEquiv B hB x = B.mulVec x := rfl

/-- Exact determinant Jacobian on the coordinate carrier, also for complex-valued integrands. -/
theorem integral_comp_matrix_mulVec {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : Mat d) (hB : B.det ≠ 0) (f : Vec d → E) :
    (∫ x : Vec d, f (B.mulVec x)) = |B.det|⁻¹ • ∫ x : Vec d, f x := by
  have h := integral_map_equiv (μ := (volume : Measure (Vec d)))
    (matrixMeasurableEquiv B hB) f
  have hm : Measure.map (matrixMeasurableEquiv B hB) volume =
      ENNReal.ofReal |B.det⁻¹| • (volume : Measure (Vec d)) :=
    Real.map_matrix_volume_pi_eq_smul_volume_pi hB
  rw [hm, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _)] at h
  simpa only [matrixMeasurableEquiv_apply, abs_inv] using h.symm

/-- An invertible matrix preserves integrability, with no substitution of volume measures. -/
theorem integrable_comp_matrix_mulVec_iff {E : Type*} [NormedAddCommGroup E]
    (B : Mat d) (hB : B.det ≠ 0) (f : Vec d → E) :
    Integrable (fun x : Vec d => f (B.mulVec x)) ↔ Integrable f := by
  have hm : Measure.map (matrixMeasurableEquiv B hB) volume =
      ENNReal.ofReal |B.det⁻¹| • (volume : Measure (Vec d)) :=
    Real.map_matrix_volume_pi_eq_smul_volume_pi hB
  have h := integrable_map_equiv (μ := (volume : Measure (Vec d)))
    (matrixMeasurableEquiv B hB) f
  rw [hm, integrable_smul_measure (by
    exact ENNReal.ofReal_ne_zero_iff.mpr (abs_pos.mpr (inv_ne_zero hB))) ENNReal.ofReal_ne_top] at h
  simpa only [Function.comp_def, matrixMeasurableEquiv_apply] using h.symm

/-- The positive matrix square root used only in the Lebesgue change of variables. -/
noncomputable def gaussianCovarianceSqrt (A : Mat d) : Mat d := CFC.sqrt A

/-- Positive definiteness of the change-of-variables matrix. -/
theorem posDef_gaussianCovarianceSqrt (A : Mat d) (hA : A.PosDef) :
    (gaussianCovarianceSqrt A).PosDef :=
  Matrix.isStrictlyPositive_iff_posDef.mp hA.isStrictlyPositive.sqrt

/-- Its square is the full covariance matrix. -/
theorem gaussianCovarianceSqrt_mul_self (A : Mat d) (hA : A.PosDef) :
    gaussianCovarianceSqrt A * gaussianCovarianceSqrt A = A :=
  CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg

/-- Symmetry of the positive change-of-variables matrix. -/
theorem transpose_gaussianCovarianceSqrt (A : Mat d) (hA : A.PosDef) :
    (gaussianCovarianceSqrt A).transpose = gaussianCovarianceSqrt A := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (posDef_gaussianCovarianceSqrt A hA).isHermitian.eq

/-- Its Jacobian is precisely the square root in the frozen normalization. -/
theorem det_gaussianCovarianceSqrt (A : Mat d) (hA : A.PosDef) :
    (gaussianCovarianceSqrt A).det = Real.sqrt A.det := by
  have hp := (posDef_gaussianCovarianceSqrt A hA).det_pos
  have hsq := congrArg Matrix.det (gaussianCovarianceSqrt_mul_self A hA)
  rw [Matrix.det_mul] at hsq
  rw [← hsq, Real.sqrt_mul_self hp.le]

/-- Whitening cancels the actual inverse quadratic form, without changing carriers. -/
theorem quadratic_inv_mulVec_gaussianCovarianceSqrt (A : Mat d) (hA : A.PosDef)
    (x : Vec d) :
    (∑ j, ∑ k, (gaussianCovarianceSqrt A).mulVec x j * (A⁻¹) j k *
      (gaussianCovarianceSqrt A).mulVec x k) = ∑ j, (x j) ^ 2 := by
  let B := gaussianCovarianceSqrt A
  have hB : B.transpose = B := transpose_gaussianCovarianceSqrt A hA
  have hBA : B * A⁻¹ * B = 1 := by
    have hBunit : IsUnit B.det :=
      isUnit_iff_ne_zero.mpr (posDef_gaussianCovarianceSqrt A hA).det_pos.ne'
    have hBsq : B * B = A := gaussianCovarianceSqrt_mul_self A hA
    calc
      B * A⁻¹ * B = B * (B⁻¹ * B⁻¹) * B := by rw [← hBsq, Matrix.mul_inv_rev]
      _ = (B * B⁻¹) * (B⁻¹ * B) := by noncomm_ring
      _ = 1 := by
        rw [Matrix.mul_nonsing_inv B hBunit, Matrix.nonsing_inv_mul B hBunit, one_mul]
  have hq (y : Vec d) : (∑ j, ∑ k, y j * (A⁻¹) j k * y k) =
      y ⬝ᵥ (A⁻¹).mulVec y := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  rw [hq]
  change (B.mulVec x) ⬝ᵥ (A⁻¹).mulVec (B.mulVec x) = _
  nth_rw 1 [← Matrix.vecMul_transpose]
  rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    hB, hBA, Matrix.one_mulVec]
  simp only [dotProduct, pow_two]

private lemma gaussian_prefactor_eq_prod (s : ℝ) (hs : 0 < s) :
    (2 * Real.pi * s) ^ (-(d : ℝ) / 2) =
      ∏ _j : Fin d, (Real.sqrt (2 * Real.pi * s))⁻¹ := by
  have hp : 0 ≤ 2 * Real.pi * s := (mul_pos (mul_pos (by norm_num) Real.pi_pos) hs).le
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.rpow_natCast,
    Real.sqrt_eq_rpow, ← Real.rpow_neg hp, ← Real.rpow_mul hp]
  congr 1
  ring

/-- The density after the exact covariance change of variables is a product of real Gaussian pdfs. -/
theorem anisotropicGaussian_mulVec_gaussianCovarianceSqrt
    (A : Mat d) (hA : A.PosDef) (s : ℝ) (hs : 0 < s) (x : Vec d) :
    anisotropicGaussian A s ((gaussianCovarianceSqrt A).mulVec x) =
      (Real.sqrt A.det)⁻¹ *
        ∏ j, ProbabilityTheory.gaussianPDFReal 0 ⟨s, hs.le⟩ (x j) := by
  rw [anisotropicGaussian, quadratic_inv_mulVec_gaussianCovarianceSqrt A hA,
    gaussian_prefactor_eq_prod s hs]
  simp only [ProbabilityTheory.gaussianPDFReal, sub_zero, Finset.prod_mul_distrib,
    ← Real.exp_sum, ← Finset.sum_div, ← Finset.sum_neg_distrib, NNReal.coe_mk]
  change (∏ _ : Fin d, (Real.sqrt (2 * Real.pi * s))⁻¹) /
    Real.sqrt A.det * Real.exp ((∑ j, -x j ^ 2) / (2 * s)) =
    (Real.sqrt A.det)⁻¹ * ((∏ _ : Fin d, (Real.sqrt (2 * Real.pi * s))⁻¹) *
      Real.exp ((∑ j, -x j ^ 2) / (2 * s)))
  ring

/-- Genuine Lebesgue integrability of the anisotropic density for every positive time. -/
theorem integrable_anisotropicGaussian (A : Mat d) (hA : A.PosDef) (s : ℝ) (hs : 0 < s) :
    Integrable (anisotropicGaussian A s) := by
  rw [← integrable_comp_matrix_mulVec_iff (gaussianCovarianceSqrt A)
    (posDef_gaussianCovarianceSqrt A hA).det_pos.ne']
  simp_rw [anisotropicGaussian_mulVec_gaussianCovarianceSqrt A hA s hs]
  exact (Integrable.fintype_prod (fun _j : Fin d =>
    ProbabilityTheory.integrable_gaussianPDFReal 0 ⟨s, hs.le⟩)).const_mul _

/-- The determinant/inverse density with covariance `s A` has total mass one. -/
theorem integral_anisotropicGaussian (A : Mat d) (hA : A.PosDef) (s : ℝ) (hs : 0 < s) :
    (∫ x : Vec d, anisotropicGaussian A s x) = 1 := by
  have h := integral_comp_matrix_mulVec (gaussianCovarianceSqrt A)
    (posDef_gaussianCovarianceSqrt A hA).det_pos.ne' (anisotropicGaussian A s)
  simp_rw [anisotropicGaussian_mulVec_gaussianCovarianceSqrt A hA s hs] at h
  rw [integral_const_mul, integral_fintype_prod_volume_eq_prod] at h
  have hv : (⟨s, hs.le⟩ : NNReal) ≠ 0 := by
    intro hh
    exact hs.ne' (congrArg (fun u : NNReal => (u : ℝ)) hh)
  simp only [ProbabilityTheory.integral_gaussianPDFReal_eq_one 0 hv, Finset.prod_const_one,
    mul_one, det_gaussianCovarianceSqrt A hA, abs_of_pos (Real.sqrt_pos.mpr hA.det_pos),
    smul_eq_mul] at h
  apply mul_left_cancel₀ (inv_ne_zero (Real.sqrt_pos.mpr hA.det_pos).ne')
  simpa only [mul_one] using h.symm

private lemma gaussian_quadratic_complete_square (B : Mat d)
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (x y : Vec d) :
    -(∑ j, ∑ k, (x - y) j * B j k * (x - y) k) / (2 * s) -
        (∑ j, ∑ k, y j * B j k * y k) / (2 * t) =
      -(∑ j, ∑ k, x j * B j k * x k) / (2 * (s + t)) -
        (∑ j, ∑ k, (y - (t / (s + t)) • x) j * B j k *
          (y - (t / (s + t)) • x) k) / (2 * (s * t / (s + t))) := by
  have hst : s + t ≠ 0 := (add_pos hs ht).ne'
  simp only [neg_div, Finset.sum_div]
  simp only [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  field_simp
  ring

private lemma gaussian_prefactor_mul (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    (2 * Real.pi * s) ^ (-(d : ℝ) / 2) * (2 * Real.pi * t) ^ (-(d : ℝ) / 2) =
      (2 * Real.pi * (s + t)) ^ (-(d : ℝ) / 2) *
        (2 * Real.pi * (s * t / (s + t))) ^ (-(d : ℝ) / 2) := by
  have hp : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  rw [← Real.mul_rpow (mul_pos hp hs).le (mul_pos hp ht).le,
    ← Real.mul_rpow (mul_pos hp (add_pos hs ht)).le
      (mul_pos hp (div_pos (mul_pos hs ht) (add_pos hs ht))).le]
  congr 1
  field_simp

/-- The exact product formula with the Brownian-bridge time `s*t/(s+t)`.
It retains every inverse-matrix entry and needs no isotropic reduction. -/
theorem anisotropicGaussian_mul_complete_square (A : Mat d)
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (x y : Vec d) :
    anisotropicGaussian A s (x - y) * anisotropicGaussian A t y =
      anisotropicGaussian A (s + t) x *
        anisotropicGaussian A (s * t / (s + t)) (y - (t / (s + t)) • x) := by
  have hmul (a b c u v : ℝ) :
      (a / c * Real.exp u) * (b / c * Real.exp v) =
        (a * b / c ^ 2) * Real.exp (u + v) := by
    rw [Real.exp_add]
    ring
  unfold anisotropicGaussian
  rw [hmul, gaussian_prefactor_mul s t hs ht]
  have hq := gaussian_quadratic_complete_square (A⁻¹) s t hs ht x y
  conv at hq => lhs; rw [sub_eq_add_neg, ← neg_div]
  conv at hq => rhs; rw [sub_eq_add_neg, ← neg_div]
  rw [hq, Real.exp_add]
  ring

/-- The pointwise product in the convolution is genuinely Lebesgue integrable. -/
theorem integrable_anisotropicGaussian_convolution (A : Mat d) (hA : A.PosDef)
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (x : Vec d) :
    Integrable (fun y : Vec d => anisotropicGaussian A s (x - y) *
      anisotropicGaussian A t y) := by
  simp_rw [anisotropicGaussian_mul_complete_square A s t hs ht x]
  exact ((integrable_anisotropicGaussian A hA (s * t / (s + t))
    (div_pos (mul_pos hs ht) (add_pos hs ht))).comp_sub_right
      ((t / (s + t)) • x)).const_mul _

/-- Anisotropic Gaussian convolution, with covariance `(s+t) A` and the literal normalization. -/
theorem integral_anisotropicGaussian_convolution (A : Mat d) (hA : A.PosDef)
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (x : Vec d) :
    (∫ y : Vec d, anisotropicGaussian A s (x - y) * anisotropicGaussian A t y) =
      anisotropicGaussian A (s + t) x := by
  simp_rw [anisotropicGaussian_mul_complete_square A s t hs ht x]
  rw [integral_const_mul, integral_sub_right_eq_self,
    integral_anisotropicGaussian A hA _ (div_pos (mul_pos hs ht) (add_pos hs ht)), mul_one]

private lemma quadratic_inverse_mixed_force {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) (x : Vec d) :
    (∑ j, ∑ k, x j * ((homogenizedCoefficient Q)⁻¹) j k *
      (homogenizedCoefficient Q).mulVec (unitVector i) k) = x i := by
  have hi : ((homogenizedCoefficient Q)⁻¹).mulVec
      ((homogenizedCoefficient Q).mulVec (unitVector i)) = unitVector i := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _
      (isUnit_iff_ne_zero.mpr (det_homogenizedCoefficient_pos Q).ne'), Matrix.one_mulVec]
  calc
    _ = x ⬝ᵥ ((homogenizedCoefficient Q)⁻¹).mulVec
        ((homogenizedCoefficient Q).mulVec (unitVector i)) := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
    _ = _ := by rw [hi]; simp [dotProduct, unitVector, Pi.single_apply, mul_ite]

private lemma quadratic_complex_force_shift {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) (u : ℂ) (x : Vec d) :
    (∑ j, ∑ k,
      ((x j : ℂ) - u * ((homogenizedCoefficient Q).mulVec (unitVector i) j : ℂ)) *
        (((homogenizedCoefficient Q)⁻¹) j k : ℂ) *
          ((x k : ℂ) - u * ((homogenizedCoefficient Q).mulVec (unitVector i) k : ℂ))) =
      ((∑ j, ∑ k, x j * ((homogenizedCoefficient Q)⁻¹) j k * x k : ℝ) : ℂ) -
        2 * u * (x i : ℂ) + u ^ 2 * (homogenizedCoefficient Q i i : ℂ) := by
  let A := homogenizedCoefficient Q
  let v := A.mulVec (unitVector i)
  have hB : (A⁻¹).transpose = A⁻¹ := by
    rw [Matrix.transpose_nonsing_inv]
    change (homogenizedMatrix Q).transpose⁻¹ = _
    rw [homogenizedMatrix_transpose Q]
    rfl
  have hxb (y : Vec d) : (∑ j, ∑ k, (y j : ℂ) * ((A⁻¹) j k : ℂ) * (v k : ℂ)) =
      (y i : ℂ) := by
    simpa only [Complex.ofReal_sum, Complex.ofReal_mul] using
      congrArg Complex.ofReal (quadratic_inverse_mixed_force Q i y)
  have hvb : (∑ j, ∑ k, (v j : ℂ) * ((A⁻¹) j k : ℂ) * (x k : ℂ)) = (x i : ℂ) := by
    rw [← hxb x, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    have hs : (A⁻¹) k j = (A⁻¹) j k := congrFun (congrFun hB j) k
    rw [hs]
    ring
  have hvv : (∑ j, ∑ k, (v j : ℂ) * ((A⁻¹) j k : ℂ) * (v k : ℂ)) = (A i i : ℂ) := by
    rw [hxb]
    simp [v, unitVector]
  change (∑ j, ∑ k, ((x j : ℂ) - u * (v j : ℂ)) * ((A⁻¹) j k : ℂ) *
    ((x k : ℂ) - u * (v k : ℂ))) = _
  calc
    _ = (∑ j, ∑ k, (x j : ℂ) * ((A⁻¹) j k : ℂ) * (x k : ℂ)) -
        u * (∑ j, ∑ k, (x j : ℂ) * ((A⁻¹) j k : ℂ) * (v k : ℂ)) -
        u * (∑ j, ∑ k, (v j : ℂ) * ((A⁻¹) j k : ℂ) * (x k : ℂ)) +
        u ^ 2 * (∑ j, ∑ k, (v j : ℂ) * ((A⁻¹) j k : ℂ) * (v k : ℂ)) := by
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by
      rw [hxb, hvb, hvv]
      simp only [Complex.ofReal_sum, Complex.ofReal_mul]
      ring

/-- Entire-force tilt of the actual kernel. The inverse and drift cancellation use the
actual symmetric, positive definite variational homogenized coefficient. -/
theorem homogenizedGaussianKernel_eq_exp_tilt {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (s : ℝ) (hs : 0 < s) (ζ : ℂ) (x : Vec d) :
    homogenizedGaussianKernel Q i s hs ζ x =
      Complex.exp (ζ * (x i : ℂ) - ζ ^ 2 * (s : ℂ) * (homogenizedCoefficient Q i i : ℂ) / 2) *
        (anisotropicGaussian (homogenizedCoefficient Q) s x : ℂ) := by
  unfold homogenizedGaussianKernel
  dsimp only
  rw [quadratic_complex_force_shift Q i (ζ * (s : ℂ)) x]
  have he (q a b : ℂ) :
      -(q - 2 * (ζ * (s : ℂ)) * a + (ζ * (s : ℂ)) ^ 2 * b) / (2 * (s : ℂ)) =
        (ζ * a - ζ ^ 2 * (s : ℂ) * b / 2) + (-q / (2 * (s : ℂ))) := by
    field_simp [Complex.ofReal_ne_zero.mpr hs.ne']
    ring
  rw [he, Complex.exp_add]
  simp only [anisotropicGaussian, Complex.ofReal_mul, Complex.ofReal_exp,
    Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_ofNat]
  ring

private lemma homogenizedGaussianKernel_product_tilt {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (ζ : ℂ) (x y : Vec d) :
    homogenizedGaussianKernel Q i s hs ζ (x - y) *
        homogenizedGaussianKernel Q i t ht ζ y =
      Complex.exp (ζ * (x i : ℂ) - ζ ^ 2 * ((s + t : ℝ) : ℂ) *
        (homogenizedCoefficient Q i i : ℂ) / 2) *
          ((anisotropicGaussian (homogenizedCoefficient Q) s (x - y) *
            anisotropicGaussian (homogenizedCoefficient Q) t y : ℝ) : ℂ) := by
  rw [homogenizedGaussianKernel_eq_exp_tilt, homogenizedGaussianKernel_eq_exp_tilt]
  simp only [Pi.sub_apply, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul]
  rw [show Complex.exp (ζ * ((x i : ℂ) - (y i : ℂ)) -
        ζ ^ 2 * (s : ℂ) * (homogenizedCoefficient Q i i : ℂ) / 2) *
      (anisotropicGaussian (homogenizedCoefficient Q) s (x - y) : ℂ) *
        (Complex.exp (ζ * (y i : ℂ) -
          ζ ^ 2 * (t : ℂ) * (homogenizedCoefficient Q i i : ℂ) / 2) *
            (anisotropicGaussian (homogenizedCoefficient Q) t y : ℂ)) =
      (Complex.exp (ζ * ((x i : ℂ) - (y i : ℂ)) -
        ζ ^ 2 * (s : ℂ) * (homogenizedCoefficient Q i i : ℂ) / 2) *
        Complex.exp (ζ * (y i : ℂ) -
          ζ ^ 2 * (t : ℂ) * (homogenizedCoefficient Q i i : ℂ) / 2)) *
            ((anisotropicGaussian (homogenizedCoefficient Q) s (x - y) : ℂ) *
              (anisotropicGaussian (homogenizedCoefficient Q) t y : ℂ)) by ring]
  rw [← Complex.exp_add]
  congr 2
  ring

/-- Absolute Lebesgue integrability of the bilinear kernel product for every complex force. -/
theorem integrable_homogenizedGaussianKernel_convolution {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (ζ : ℂ) (x : Vec d) :
    Integrable (fun y : Vec d => homogenizedGaussianKernel Q i s hs ζ (x - y) *
      homogenizedGaussianKernel Q i t ht ζ y) := by
  simp_rw [homogenizedGaussianKernel_product_tilt Q i s t hs ht ζ x]
  exact ((integrable_anisotropicGaussian_convolution (homogenizedCoefficient Q)
    (posDef_homogenizedCoefficient Q) s t hs ht x).ofReal).const_mul _

/-- The bilinear convolution identity on the literal frozen kernel, for arbitrary complex force.
No complex conjugation or analytic-continuation premise occurs. -/
theorem integral_homogenizedGaussianKernel_convolution {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (ζ : ℂ) (x : Vec d) :
    (∫ y : Vec d, homogenizedGaussianKernel Q i s hs ζ (x - y) *
      homogenizedGaussianKernel Q i t ht ζ y) =
        homogenizedGaussianKernel Q i (s + t) (add_pos hs ht) ζ x := by
  simp_rw [homogenizedGaussianKernel_product_tilt Q i s t hs ht ζ x]
  rw [integral_const_mul, integral_complex_ofReal,
    integral_anisotropicGaussian_convolution _ (posDef_homogenizedCoefficient Q) s t hs ht x,
    homogenizedGaussianKernel_eq_exp_tilt]

private lemma integrable_sq_mul_gaussianPDF (s : ℝ) (hs : 0 < s) :
    Integrable (fun x : ℝ => x ^ 2 * ProbabilityTheory.gaussianPDFReal 0 ⟨s, hs.le⟩ x) := by
  let v : NNReal := ⟨s, hs.le⟩
  have hv : v ≠ 0 := by
    intro hh
    exact hs.ne' (congrArg (fun u : NNReal => (u : ℝ)) hh)
  have h := (ProbabilityTheory.memLp_id_gaussianReal (μ := 0) (v := v) 2).integrable_sq
  rw [ProbabilityTheory.gaussianReal_of_var_ne_zero 0 hv,
    integrable_withDensity_iff_integrable_smul'
      (ProbabilityTheory.measurable_gaussianPDF 0 v)
      (Filter.Eventually.of_forall (fun _ => ProbabilityTheory.gaussianPDF_lt_top))] at h
  simpa only [ProbabilityTheory.gaussianPDF, ENNReal.toReal_ofReal
    (ProbabilityTheory.gaussianPDFReal_nonneg 0 v _), smul_eq_mul, id_eq, mul_comm] using h

private lemma integrable_sq_coordinate_mul_gaussianProduct (s : ℝ) (hs : 0 < s) (j : Fin d) :
    Integrable (fun x : Vec d => x j ^ 2 *
      ∏ a, ProbabilityTheory.gaussianPDFReal 0 ⟨s, hs.le⟩ (x a)) := by
  have h (a : Fin d) : Integrable (fun u : ℝ =>
      (if a = j then u ^ 2 else 1) * ProbabilityTheory.gaussianPDFReal 0 ⟨s, hs.le⟩ u) := by
    by_cases ha : a = j
    · simpa only [ha, if_true] using integrable_sq_mul_gaussianPDF s hs
    · simpa only [ha, if_false, one_mul] using
        ProbabilityTheory.integrable_gaussianPDFReal 0 ⟨s, hs.le⟩
  simpa only [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true]
    using! Integrable.fintype_prod h

private lemma integrable_sq_mulVec_mul_gaussianProduct
    (M : Mat d) (j : Fin d) (s : ℝ) (hs : 0 < s) :
    Integrable (fun x : Vec d => (M.mulVec x j) ^ 2 *
      ∏ a, ProbabilityTheory.gaussianPDFReal 0 ⟨s, hs.le⟩ (x a)) := by
  have hsum : Integrable (fun x : Vec d => (∑ a, x a ^ 2) *
      ∏ a, ProbabilityTheory.gaussianPDFReal 0 ⟨s, hs.le⟩ (x a)) := by
    simp_rw [Finset.sum_mul]
    exact integrable_finset_sum _ (fun a _ => integrable_sq_coordinate_mul_gaussianProduct s hs a)
  apply (hsum.const_mul (∑ a, M j a ^ 2)).mono' (by
    apply Continuous.aestronglyMeasurable
    simp only [ProbabilityTheory.gaussianPDFReal, Matrix.mulVec, dotProduct]
    fun_prop)
  apply Filter.Eventually.of_forall
  intro x
  have hp : 0 ≤ ∏ a, ProbabilityTheory.gaussianPDFReal 0 ⟨s, hs.le⟩ (x a) :=
    Finset.prod_nonneg (fun a _ => ProbabilityTheory.gaussianPDFReal_nonneg _ _ _)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hp)]
  rw [← mul_assoc]
  apply mul_le_mul_of_nonneg_right _ hp
  exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (M j) x

private lemma integrable_mulVec_mul_gaussianProduct
    (M : Mat d) (j : Fin d) (s : ℝ) (hs : 0 < s) :
    Integrable (fun x : Vec d => M.mulVec x j *
      ∏ a, ProbabilityTheory.gaussianPDFReal 0 ⟨s, hs.le⟩ (x a)) := by
  have h0 := Integrable.fintype_prod (fun _a : Fin d =>
    ProbabilityTheory.integrable_gaussianPDFReal 0 ⟨s, hs.le⟩)
  apply ((integrable_sq_mulVec_mul_gaussianProduct M j s hs).add h0).mono' (by
    apply Continuous.aestronglyMeasurable
    simp only [ProbabilityTheory.gaussianPDFReal, Matrix.mulVec, dotProduct]
    fun_prop)
  apply Filter.Eventually.of_forall
  intro x
  have hp : 0 ≤ ∏ a, ProbabilityTheory.gaussianPDFReal 0 ⟨s, hs.le⟩ (x a) :=
    Finset.prod_nonneg (fun a _ => ProbabilityTheory.gaussianPDFReal_nonneg _ _ _)
  simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hp, Pi.add_apply]
  calc
    _ ≤ ((M.mulVec x j) ^ 2 + 1) *
        (∏ a, ProbabilityTheory.gaussianPDFReal 0 ⟨s, hs.le⟩ (x a)) := ?_
    _ = _ := by ring
  · have hbound : |M.mulVec x j| ≤ (M.mulVec x j) ^ 2 + 1 := by
      nlinarith [sq_nonneg (|M.mulVec x j| - 1), sq_abs (M.mulVec x j)]
    exact mul_le_mul_of_nonneg_right hbound hp

private lemma integrable_mulVec_mulVec_mul_gaussianProduct
    (M N : Mat d) (j k : Fin d) (s : ℝ) (hs : 0 < s) :
    Integrable (fun x : Vec d => M.mulVec x j * N.mulVec x k *
      ∏ a, ProbabilityTheory.gaussianPDFReal 0 ⟨s, hs.le⟩ (x a)) := by
  apply ((integrable_sq_mulVec_mul_gaussianProduct M j s hs).add
    (integrable_sq_mulVec_mul_gaussianProduct N k s hs)).mono' (by
    apply Continuous.aestronglyMeasurable
    simp only [ProbabilityTheory.gaussianPDFReal, Matrix.mulVec, dotProduct]
    fun_prop)
  apply Filter.Eventually.of_forall
  intro x
  have hp : 0 ≤ ∏ a, ProbabilityTheory.gaussianPDFReal 0 ⟨s, hs.le⟩ (x a) :=
    Finset.prod_nonneg (fun a _ => ProbabilityTheory.gaussianPDFReal_nonneg _ _ _)
  simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hp, Pi.add_apply]
  rw [← add_mul]
  apply mul_le_mul_of_nonneg_right _ hp
  nlinarith [sq_nonneg (|M.mulVec x j| - |N.mulVec x k|), sq_abs (M.mulVec x j),
    sq_abs (N.mulVec x k), mul_self_nonneg (M.mulVec x j), mul_self_nonneg (N.mulVec x k)]

/-- First linear moments of the actual anisotropic density are absolutely integrable. -/
theorem integrable_mulVec_mul_anisotropicGaussian (A : Mat d) (hA : A.PosDef)
    (M : Mat d) (j : Fin d) (s : ℝ) (hs : 0 < s) :
    Integrable (fun x : Vec d => M.mulVec x j * anisotropicGaussian A s x) := by
  rw [← integrable_comp_matrix_mulVec_iff (gaussianCovarianceSqrt A)
    (posDef_gaussianCovarianceSqrt A hA).det_pos.ne']
  simp_rw [anisotropicGaussian_mulVec_gaussianCovarianceSqrt A hA s hs,
    Matrix.mulVec_mulVec]
  convert (integrable_mulVec_mul_gaussianProduct (M * gaussianCovarianceSqrt A) j s hs).const_mul
    (Real.sqrt A.det)⁻¹ using 1
  funext x
  ring

/-- Products of two linear moments are absolutely integrable against the anisotropic density. -/
theorem integrable_mulVec_mulVec_mul_anisotropicGaussian (A : Mat d) (hA : A.PosDef)
    (M N : Mat d) (j k : Fin d) (s : ℝ) (hs : 0 < s) :
    Integrable (fun x : Vec d => M.mulVec x j * N.mulVec x k * anisotropicGaussian A s x) := by
  rw [← integrable_comp_matrix_mulVec_iff (gaussianCovarianceSqrt A)
    (posDef_gaussianCovarianceSqrt A hA).det_pos.ne']
  simp_rw [anisotropicGaussian_mulVec_gaussianCovarianceSqrt A hA s hs,
    Matrix.mulVec_mulVec]
  convert (integrable_mulVec_mulVec_mul_gaussianProduct
    (M * gaussianCovarianceSqrt A) (N * gaussianCovarianceSqrt A) j k s hs).const_mul
      (Real.sqrt A.det)⁻¹ using 1
  funext x
  ring

/-- Evenness in the spatial displacement, with the full inverse matrix. -/
theorem anisotropicGaussian_neg (A : Mat d) (s : ℝ) (x : Vec d) :
    anisotropicGaussian A s (-x) = anisotropicGaussian A s x := by
  simp only [anisotropicGaussian, Pi.neg_apply, neg_mul, mul_neg, neg_neg]

/-- Every linear first moment of the centered anisotropic density vanishes. -/
theorem integral_mulVec_mul_anisotropicGaussian (A M : Mat d) (j : Fin d) (s : ℝ) :
    (∫ x : Vec d, M.mulVec x j * anisotropicGaussian A s x) = 0 := by
  have h := integral_neg_eq_self (fun x : Vec d => M.mulVec x j * anisotropicGaussian A s x)
    (volume : Measure (Vec d))
  simp only [Matrix.mulVec_neg, Pi.neg_apply, anisotropicGaussian_neg, neg_mul, integral_neg] at h
  linarith

private lemma fderiv_mulVec_entry (M : Mat d) (j k : Fin d) (x : Vec d) :
    fderiv ℝ (fun y : Vec d => M.mulVec y j) x (unitVector k) = M j k := by
  change fderiv ℝ (fun y : Vec d => ∑ a, M j a * y a) x (unitVector k) = _
  rw [fderiv_fun_sum (fun a _ => by fun_prop)]
  simp only [ContinuousLinearMap.sum_apply]
  have he (a : Fin d) :
      fderiv ℝ (fun y : Vec d => M j a * y a) x (unitVector k) = M j a * unitVector k a := by
    rw [fderiv_const_mul (by fun_prop)]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul,
      (hasFDerivAt_apply (𝕜 := ℝ) a x).fderiv, ContinuousLinearMap.proj_apply]
  simp_rw [he]
  simp [unitVector, Pi.single_apply, mul_ite]

/-- The inverse-weighted Gaussian second moment, proved by genuine Lebesgue integration by parts. -/
theorem integral_inv_mulVec_mulVec_mul_anisotropicGaussian
    (A : Mat d) (hA : A.PosDef) (j k : Fin d) (s : ℝ) (hs : 0 < s) :
    (∫ x : Vec d, (A⁻¹).mulVec x j * (A⁻¹).mulVec x k * anisotropicGaussian A s x) =
      s * (A⁻¹) j k := by
  have hsym : A.transpose = A := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.isHermitian.eq
  have hf : Differentiable ℝ (fun x : Vec d => (A⁻¹).mulVec x j) := by
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  have hg := (contDiff_anisotropicGaussian A s).differentiable (by simp)
  have hf'g : Integrable (fun x : Vec d =>
      fderiv ℝ (fun y : Vec d => (A⁻¹).mulVec y j) x (unitVector k) *
        anisotropicGaussian A s x) := by
    simp_rw [fderiv_mulVec_entry]
    exact (integrable_anisotropicGaussian A hA s hs).const_mul _
  have hfg' : Integrable (fun x : Vec d => (A⁻¹).mulVec x j *
      fderiv ℝ (anisotropicGaussian A s) x (unitVector k)) := by
    simp_rw [fderiv_anisotropicGaussian_coordinate A hsym]
    convert (integrable_mulVec_mulVec_mul_anisotropicGaussian A hA (A⁻¹) (A⁻¹) j k s hs
      ).const_mul (-1 / s) using 1
    funext x
    ring
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hf'g hfg'
    (integrable_mulVec_mul_anisotropicGaussian A hA (A⁻¹) j s hs) (fun x _ => hf x) (fun x _ => hg x)
  simp_rw [fderiv_mulVec_entry, fderiv_anisotropicGaussian_coordinate A hsym] at h
  rw [show (fun x : Vec d => (A⁻¹).mulVec x j *
      (-((A⁻¹).mulVec x k) / s * anisotropicGaussian A s x)) =
        (fun x => (-1 / s) * ((A⁻¹).mulVec x j * (A⁻¹).mulVec x k *
          anisotropicGaussian A s x)) by funext x; ring,
    integral_const_mul, integral_const_mul, integral_anisotropicGaussian A hA s hs, mul_one] at h
  field_simp at h
  linarith

private lemma gaussianAffineProduct_expand (A : Mat d) (j k : Fin d) (s : ℝ)
    (a b c e : ℂ) :
    (fun x : Vec d => (a + b * ((A⁻¹).mulVec x j : ℂ)) *
      (c + e * ((A⁻¹).mulVec x k : ℂ)) * (anisotropicGaussian A s x : ℂ)) =
    (fun x => (a * c) * (anisotropicGaussian A s x : ℂ)) +
      (fun x => (b * c) * (( (A⁻¹).mulVec x j * anisotropicGaussian A s x : ℝ) : ℂ)) +
      (fun x => (a * e) * (( (A⁻¹).mulVec x k * anisotropicGaussian A s x : ℝ) : ℂ)) +
      (fun x => (b * e) * (( (A⁻¹).mulVec x j * (A⁻¹).mulVec x k *
        anisotropicGaussian A s x : ℝ) : ℂ)) := by
  funext x
  simp only [Pi.add_apply, Complex.ofReal_mul]
  ring

private lemma integrable_gaussianAffineProduct (A : Mat d) (hA : A.PosDef)
    (j k : Fin d) (s : ℝ) (hs : 0 < s) (a b c e : ℂ) :
    Integrable (fun x : Vec d => (a + b * ((A⁻¹).mulVec x j : ℂ)) *
      (c + e * ((A⁻¹).mulVec x k : ℂ)) * (anisotropicGaussian A s x : ℂ)) := by
  rw [gaussianAffineProduct_expand]
  exact ((((integrable_anisotropicGaussian A hA s hs).ofReal.const_mul (a * c)).add
    ((integrable_mulVec_mul_anisotropicGaussian A hA (A⁻¹) j s hs).ofReal.const_mul (b * c))).add
      ((integrable_mulVec_mul_anisotropicGaussian A hA (A⁻¹) k s hs).ofReal.const_mul (a * e))).add
        ((integrable_mulVec_mulVec_mul_anisotropicGaussian A hA (A⁻¹) (A⁻¹) j k s hs
          ).ofReal.const_mul (b * e))

private lemma integral_gaussianAffineProduct (A : Mat d) (hA : A.PosDef)
    (j k : Fin d) (s : ℝ) (hs : 0 < s) (a b c e : ℂ) :
    (∫ x : Vec d, (a + b * ((A⁻¹).mulVec x j : ℂ)) *
      (c + e * ((A⁻¹).mulVec x k : ℂ)) * (anisotropicGaussian A s x : ℂ)) =
        a * c + b * e * (s : ℂ) * ((A⁻¹) j k : ℂ) := by
  have h0 := (integrable_anisotropicGaussian A hA s hs).ofReal.const_mul (a * c)
  have hj := (integrable_mulVec_mul_anisotropicGaussian A hA (A⁻¹) j s hs).ofReal.const_mul (b * c)
  have hk := (integrable_mulVec_mul_anisotropicGaussian A hA (A⁻¹) k s hs).ofReal.const_mul (a * e)
  have hjk := (integrable_mulVec_mulVec_mul_anisotropicGaussian A hA (A⁻¹) (A⁻¹) j k s hs
    ).ofReal.const_mul (b * e)
  let f0 := fun x : Vec d => a * c * (anisotropicGaussian A s x : ℂ)
  let fj := fun x : Vec d => b * c * (( (A⁻¹).mulVec x j * anisotropicGaussian A s x : ℝ) : ℂ)
  let fk := fun x : Vec d => a * e * (( (A⁻¹).mulVec x k * anisotropicGaussian A s x : ℝ) : ℂ)
  let fjk := fun x : Vec d => b * e * (( (A⁻¹).mulVec x j * (A⁻¹).mulVec x k *
    anisotropicGaussian A s x : ℝ) : ℂ)
  have hadd : (∫ x, ((f0 x + fj x) + fk x) + fjk x) =
      ((∫ x, f0 x) + ∫ x, fj x) + (∫ x, fk x) + ∫ x, fjk x := by
    calc
      _ = (∫ x, f0 x + fj x + fk x) + ∫ x, fjk x := integral_add ((h0.add hj).add hk) hjk
      _ = ((∫ x, f0 x + fj x) + ∫ x, fk x) + ∫ x, fjk x :=
        congrArg (fun z => z + ∫ x, fjk x) (integral_add (h0.add hj) hk)
      _ = _ := congrArg (fun z => (z + ∫ x, fk x) + ∫ x, fjk x) (integral_add h0 hj)
  rw [gaussianAffineProduct_expand]
  change (∫ x, ((f0 x + fj x) + fk x) + fjk x) = _
  rw [hadd]
  dsimp only [f0, fj, fk, fjk]
  simp only [integral_const_mul, integral_complex_ofReal]
  rw [integral_anisotropicGaussian A hA s hs,
    integral_mulVec_mul_anisotropicGaussian, integral_mulVec_mul_anisotropicGaussian,
    integral_inv_mulVec_mulVec_mul_anisotropicGaussian A hA j k s hs]
  simp only [Complex.ofReal_one, Complex.ofReal_zero, Complex.ofReal_mul,
    mul_one, mul_zero, add_zero]
  ring

/-- Reversing space reverses the force, as required by the bilinear transpose convention. -/
theorem homogenizedGaussianKernel_neg_force {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (s : ℝ) (hs : 0 < s) (ζ : ℂ) (x : Vec d) :
    homogenizedGaussianKernel Q i s hs (-ζ) x =
      homogenizedGaussianKernel Q i s hs ζ (-x) := by
  rw [homogenizedGaussianKernel_eq_exp_tilt, homogenizedGaussianKernel_eq_exp_tilt,
    anisotropicGaussian_neg]
  simp only [Pi.neg_apply, Complex.ofReal_neg, neg_mul, neg_sq, mul_neg]

private lemma homogenizedGaussianKernel_bilinear_product {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (ζ : ℂ) (y : Vec d) :
    homogenizedGaussianKernel Q i s hs (-ζ) y * homogenizedGaussianKernel Q i t ht ζ y =
      homogenizedGaussianKernel Q i (s + t) (add_pos hs ht) ζ 0 *
        (anisotropicGaussian (homogenizedCoefficient Q) (s * t / (s + t)) y : ℂ) := by
  rw [homogenizedGaussianKernel_neg_force]
  have h := homogenizedGaussianKernel_product_tilt Q i s t hs ht ζ 0 y
  simp only [zero_sub] at h
  have hc := anisotropicGaussian_mul_complete_square (homogenizedCoefficient Q) s t hs ht 0 y
  simp only [zero_sub, smul_zero, sub_zero] at hc
  rw [h, hc]
  simp only [Complex.ofReal_mul, homogenizedGaussianKernel_eq_exp_tilt, Pi.zero_apply]
  ring

private lemma bilinear_derivative_product {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i j k : Fin d)
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (ζ : ℂ) (y : Vec d) :
    fderiv ℝ (homogenizedGaussianKernel Q i s hs (-ζ)) y (unitVector j) *
        fderiv ℝ (homogenizedGaussianKernel Q i t ht ζ) y (unitVector k) =
      homogenizedGaussianKernel Q i (s + t) (add_pos hs ht) ζ 0 *
        ((-ζ * (unitVector i j : ℂ) + (-1 / (s : ℂ)) *
            (((homogenizedCoefficient Q)⁻¹).mulVec y j : ℂ)) *
          (ζ * (unitVector i k : ℂ) + (-1 / (t : ℂ)) *
            (((homogenizedCoefficient Q)⁻¹).mulVec y k : ℂ)) *
              (anisotropicGaussian (homogenizedCoefficient Q) (s * t / (s + t)) y : ℂ)) := by
  rw [fderiv_homogenizedGaussianKernel_complexForce_coordinate,
    fderiv_homogenizedGaussianKernel_complexForce_coordinate]
  have h := homogenizedGaussianKernel_bilinear_product Q i s t hs ht ζ y
  calc
    _ = ((-ζ * (unitVector i j : ℂ) - (((homogenizedCoefficient Q)⁻¹).mulVec y j : ℂ) / (s : ℂ)) *
      (ζ * (unitVector i k : ℂ) - (((homogenizedCoefficient Q)⁻¹).mulVec y k : ℂ) / (t : ℂ))) *
        (homogenizedGaussianKernel Q i s hs (-ζ) y * homogenizedGaussianKernel Q i t ht ζ y) := by ring
    _ = _ := by rw [h]; ring

/-- Integrability of the bilinear first-derivative product, for the actual opposite-force kernels. -/
theorem integrable_homogenizedGaussianKernel_bilinear_derivatives {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i j k : Fin d)
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (ζ : ℂ) :
    Integrable (fun y : Vec d =>
      fderiv ℝ (homogenizedGaussianKernel Q i s hs (-ζ)) y (unitVector j) *
        fderiv ℝ (homogenizedGaussianKernel Q i t ht ζ) y (unitVector k)) := by
  simp_rw [bilinear_derivative_product Q i j k s t hs ht ζ]
  exact (integrable_gaussianAffineProduct _ (posDef_homogenizedCoefficient Q) j k
    (s * t / (s + t)) (div_pos (mul_pos hs ht) (add_pos hs ht))
    (-ζ * (unitVector i j : ℂ)) (-1 / (s : ℂ))
    (ζ * (unitVector i k : ℂ)) (-1 / (t : ℂ))).const_mul _

/-- Opposite-force derivative contraction, retaining the transpose minus sign and time factor. -/
theorem integral_homogenizedGaussianKernel_bilinear_derivatives {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i j k : Fin d)
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (ζ : ℂ) :
    (∫ y : Vec d,
      fderiv ℝ (homogenizedGaussianKernel Q i s hs (-ζ)) y (unitVector j) *
        fderiv ℝ (homogenizedGaussianKernel Q i t ht ζ) y (unitVector k)) =
      ((((homogenizedCoefficient Q)⁻¹) j k : ℂ) / ((s + t : ℝ) : ℂ) -
        ζ ^ 2 * (unitVector i j : ℂ) * (unitVector i k : ℂ)) *
          homogenizedGaussianKernel Q i (s + t) (add_pos hs ht) ζ 0 := by
  simp_rw [bilinear_derivative_product Q i j k s t hs ht ζ]
  rw [integral_const_mul, integral_gaussianAffineProduct _ (posDef_homogenizedCoefficient Q)
    j k _ (div_pos (mul_pos hs ht) (add_pos hs ht))]
  simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_add]
  field_simp [Complex.ofReal_ne_zero.mpr hs.ne', Complex.ofReal_ne_zero.mpr ht.ne',
    Complex.ofReal_ne_zero.mpr (add_pos hs ht).ne']
  ring

private lemma bilinear_first_derivative_product {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i j : Fin d)
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (ζ : ℂ) (y : Vec d) :
    fderiv ℝ (homogenizedGaussianKernel Q i s hs (-ζ)) y (unitVector j) *
        homogenizedGaussianKernel Q i t ht ζ y =
      homogenizedGaussianKernel Q i (s + t) (add_pos hs ht) ζ 0 *
        ((-ζ * (unitVector i j : ℂ) + (-1 / (s : ℂ)) *
            (((homogenizedCoefficient Q)⁻¹).mulVec y j : ℂ)) *
          (1 + 0 * (((homogenizedCoefficient Q)⁻¹).mulVec y j : ℂ)) *
              (anisotropicGaussian (homogenizedCoefficient Q) (s * t / (s + t)) y : ℂ)) := by
  rw [fderiv_homogenizedGaussianKernel_complexForce_coordinate]
  have h := homogenizedGaussianKernel_bilinear_product Q i s t hs ht ζ y
  calc
    _ = (-ζ * (unitVector i j : ℂ) - (((homogenizedCoefficient Q)⁻¹).mulVec y j : ℂ) / (s : ℂ)) *
      (homogenizedGaussianKernel Q i s hs (-ζ) y * homogenizedGaussianKernel Q i t ht ζ y) := by ring
    _ = _ := by rw [h]; ring

/-- Absolute integrability of the bilinear first-derivative/kernel contraction. -/
theorem integrable_homogenizedGaussianKernel_bilinear_first_derivative {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i j : Fin d)
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (ζ : ℂ) :
    Integrable (fun y : Vec d =>
      fderiv ℝ (homogenizedGaussianKernel Q i s hs (-ζ)) y (unitVector j) *
        homogenizedGaussianKernel Q i t ht ζ y) := by
  simp_rw [bilinear_first_derivative_product Q i j s t hs ht ζ]
  exact (integrable_gaussianAffineProduct _ (posDef_homogenizedCoefficient Q) j j
    (s * t / (s + t)) (div_pos (mul_pos hs ht) (add_pos hs ht))
    (-ζ * (unitVector i j : ℂ)) (-1 / (s : ℂ)) 1 0).const_mul _

/-- First-derivative contraction with the transpose sign, valid for every complex force. -/
theorem integral_homogenizedGaussianKernel_bilinear_first_derivative {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i j : Fin d)
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (ζ : ℂ) :
    (∫ y : Vec d,
      fderiv ℝ (homogenizedGaussianKernel Q i s hs (-ζ)) y (unitVector j) *
        homogenizedGaussianKernel Q i t ht ζ y) =
      -ζ * (unitVector i j : ℂ) *
        homogenizedGaussianKernel Q i (s + t) (add_pos hs ht) ζ 0 := by
  simp_rw [bilinear_first_derivative_product Q i j s t hs ht ζ]
  rw [integral_const_mul, integral_gaussianAffineProduct _ (posDef_homogenizedCoefficient Q)
    j j _ (div_pos (mul_pos hs ht) (add_pos hs ht))]
  ring

/-- The half-time first-derivative convolution is the negative time-one derivative. -/
theorem integral_homogenizedGaussianKernel_half_first_derivative {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i j : Fin d) (ζ : ℂ) :
    (∫ y : Vec d,
      fderiv ℝ (homogenizedGaussianKernel Q i (1 / 2) (by norm_num) (-ζ)) y (unitVector j) *
        homogenizedGaussianKernel Q i (1 / 2) (by norm_num) ζ y) =
      -fderiv ℝ (homogenizedGaussianKernel Q i 1 (by norm_num) ζ) 0 (unitVector j) := by
  rw [integral_homogenizedGaussianKernel_bilinear_first_derivative,
    fderiv_homogenizedGaussianKernel_complexForce_at_zero]
  norm_num

/-- The half-time derivative product is the negative mixed time-one Hessian. -/
theorem integral_homogenizedGaussianKernel_half_derivatives {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i j k : Fin d) (ζ : ℂ) :
    (∫ y : Vec d,
      fderiv ℝ (homogenizedGaussianKernel Q i (1 / 2) (by norm_num) (-ζ)) y (unitVector j) *
        fderiv ℝ (homogenizedGaussianKernel Q i (1 / 2) (by norm_num) ζ) y (unitVector k)) =
      -fderiv ℝ (fun x => fderiv ℝ (homogenizedGaussianKernel Q i 1 (by norm_num) ζ)
        x (unitVector j)) 0 (unitVector k) := by
  rw [integral_homogenizedGaussianKernel_bilinear_derivatives,
    neg_fderiv_fderiv_homogenizedGaussianKernel_complexForce_at_zero]
  norm_num

/-- The actual half-time bilinear convolutions give the frozen velocity profile.
The coefficients retain both divergence factors of one half and the transpose sign. -/
theorem velocityGaussianProfile_eq_bilinear_convolution {Λ₀ r₀ : ℝ} (hd : 2 ≤ d)
    (Q : EnvironmentLaw d Λ₀ r₀)
    (covariance : Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ)
    (i : Fin d) (ζ : ℂ) :
    let first : Fin d := ⟨0, by omega⟩
    let p := homogenizedGaussianKernel Q first (1 / 2) (by norm_num) ζ
    let pTranspose := homogenizedGaussianKernel Q first (1 / 2) (by norm_num) (-ζ)
    (1 / 4 : ℂ) * (∑ j, ∑ k,
      (∫ y : Vec d, fderiv ℝ pTranspose y (unitVector j) *
        fderiv ℝ p y (unitVector k)) *
          (covariance (.inl (j, first)) (.inl (k, i)) : ℂ)) -
      ζ / 2 * (∑ j, (∫ y : Vec d, fderiv ℝ pTranspose y (unitVector j) * p y) *
        (covariance (.inl (j, first)) (.inl (first, i)) : ℂ)) =
      velocityGaussianProfile hd Q covariance i ζ := by
  dsimp only
  simp_rw [integral_homogenizedGaussianKernel_half_derivatives,
    integral_homogenizedGaussianKernel_half_first_derivative, neg_mul,
    Finset.sum_neg_distrib]
  simpa only [neg_mul, Finset.sum_neg_distrib, mul_neg, sub_neg_eq_add] using
    velocityGaussianProfile_eq_complexKernel_contraction hd Q covariance i ζ

/-- The actual half-time first-derivative convolution gives the frozen clock profile. -/
theorem clockGaussianProfile_eq_bilinear_convolution {Λ₀ r₀ : ℝ} (hd : 2 ≤ d)
    (Q : EnvironmentLaw d Λ₀ r₀)
    (covariance : Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ) (ζ : ℂ) :
    let first : Fin d := ⟨0, by omega⟩
    let p := homogenizedGaussianKernel Q first (1 / 2) (by norm_num) ζ
    let pTranspose := homogenizedGaussianKernel Q first (1 / 2) (by norm_num) (-ζ)
    (-ζ / 2 : ℂ) * (∑ j, (∫ y : Vec d, fderiv ℝ pTranspose y (unitVector j) * p y) *
      (covariance (.inl (j, first)) (.inr ()) : ℂ)) =
        clockGaussianProfile hd Q covariance ζ := by
  dsimp only
  simp_rw [integral_homogenizedGaussianKernel_half_first_derivative, neg_mul,
    Finset.sum_neg_distrib]
  simpa only [neg_div, neg_mul_neg] using
    clockGaussianProfile_eq_complexKernel_contraction hd Q covariance ζ

end EinsteinFull
