import EinsteinFull.Work.W3.GaussianConvolutionSupport
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-! Complex Gaussian Fourier moments for a positive definite real matrix.
The tilt is integrated on the real coordinate carrier. Completing the square
gives absolute integrability; whitening computes the mass; integration by
parts computes the first two moments without a contour shift. -/

noncomputable section
namespace EinsteinFull.Blueprint.GaussianFourier
open EinsteinRelation EinsteinFull MeasureTheory
open scoped BigOperators MatrixOrder

variable {d : ℕ}

/-- The quadratic form of the actual real matrix. -/
def quadratic (A : Mat d) (x : Vec d) : ℝ := x ⬝ᵥ A.mulVec x

/-- The Fourier density with the full complex drift tilt. -/
def density (A : Mat d) (i : Fin d) (z : ℂ) (x : Vec d) : ℂ :=
  Complex.exp (-(quadratic A x : ℂ) / 2 - Complex.I * z *
    ((A.mulVec (unitVector i) ⬝ᵥ x : ℝ) : ℂ))

private lemma quadratic_sub (A : Mat d) (hA : A.transpose = A)
    (x y : Vec d) :
    quadratic A (x - y) = quadratic A x - 2 * (A.mulVec y ⬝ᵥ x) + quadratic A y := by
  simp only [quadratic, Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub]
  have hxy : x ⬝ᵥ A.mulVec y = A.mulVec y ⬝ᵥ x := dotProduct_comm _ _
  have hyx : y ⬝ᵥ A.mulVec x = A.mulVec y ⬝ᵥ x := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA, dotProduct_comm]
  rw [hxy, hyx]
  ring

private lemma quadratic_unit (A : Mat d) (i : Fin d) (t : ℝ) :
    quadratic A (t • unitVector i) = t ^ 2 * A i i := by
  simp [quadratic, unitVector, dotProduct, Pi.single_apply, Matrix.mulVec, mul_ite, ite_mul]
  ring

/-- A shifted positive quadratic form controls the linear complex tilt. -/
lemma norm_density_le (A : Mat d) (hA : A.PosDef) (i : Fin d) (z : ℂ) (x : Vec d) :
    ‖density A i z x‖ ≤ Real.exp (z.im ^ 2 * A i i) *
      Real.exp (-quadratic A x / 4) := by
  have hsym : A.transpose = A := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.isHermitian.eq
  have hpos : 0 ≤ quadratic A (x - (2 * z.im) • unitVector i) :=
    hA.posSemidef.dotProduct_mulVec_nonneg _
  rw [quadratic_sub A hsym, quadratic_unit, Matrix.mulVec_smul, smul_dotProduct] at hpos
  rw [density, Complex.norm_exp, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.neg_re,
    Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    zero_mul, one_mul, sub_zero, Complex.mul_im, Complex.ofReal_im, mul_zero,
    zero_add]
  simp only [smul_eq_mul] at hpos
  nlinarith

/-- Every polynomial of coordinate degree at most two is integrable against
this complex Gaussian. The proof uses an actual positive Gaussian majorant. -/
lemma integrable_moments (A : Mat d) (hA : A.PosDef) (i : Fin d) (z : ℂ) :
    Integrable (density A i z) ∧
    (∀ j : Fin d, Integrable (fun x : Vec d => (x j : ℂ) * density A i z x)) ∧
    (∀ j k : Fin d, Integrable (fun x : Vec d => (x j : ℂ) * (x k : ℂ) * density A i z x)) := by
  let B := A⁻¹
  have hB : B.PosDef := hA.inv
  let p : ℝ := (2 * Real.pi * 2) ^ (-(d : ℝ) / 2) / Real.sqrt B.det
  have hp : 0 < p := div_pos (Real.rpow_pos_of_pos (by positivity) _)
    (Real.sqrt_pos.mpr hB.det_pos)
  have hgauss (x : Vec d) :
      Real.exp (-quadratic A x / 4) = p⁻¹ * anisotropicGaussian B 2 x := by
    unfold anisotropicGaussian
    have hAA : B⁻¹ = A := Matrix.nonsing_inv_nonsing_inv A (isUnit_iff_ne_zero.mpr hA.det_pos.ne')
    rw [hAA]
    have hq : (∑ j, ∑ k, x j * A j k * x k) = quadratic A x := by
      simp only [quadratic, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
    rw [hq]
    change _ = p⁻¹ * (p * _)
    rw [← mul_assoc, inv_mul_cancel₀ hp.ne', one_mul]
    norm_num
  have hbound (x : Vec d) := norm_density_le A hA i z x
  simp_rw [hgauss] at hbound
  have hnonneg (x : Vec d) : 0 ≤ anisotropicGaussian B 2 x := by
    unfold anisotropicGaussian
    positivity
  have h0 := (integrable_anisotropicGaussian B hB 2 (by norm_num)).const_mul
    (Real.exp (z.im ^ 2 * A i i) * p⁻¹)
  have h1 (j : Fin d) :=
    (integrable_mulVec_mul_anisotropicGaussian B hB 1 j 2 (by norm_num)).norm.const_mul
      (Real.exp (z.im ^ 2 * A i i) * p⁻¹)
  have h2 (j k : Fin d) :=
    (integrable_mulVec_mulVec_mul_anisotropicGaussian B hB 1 1 j k 2 (by norm_num)).norm.const_mul
      (Real.exp (z.im ^ 2 * A i i) * p⁻¹)
  refine ⟨h0.mono' (by unfold density quadratic Matrix.mulVec dotProduct; fun_prop)
    (Filter.Eventually.of_forall (fun x => by simpa [mul_assoc] using hbound x)), ?_, ?_⟩
  · intro j
    apply (h1 j).mono' (by unfold density quadratic Matrix.mulVec dotProduct; fun_prop)
    apply Filter.Eventually.of_forall
    intro x
    simpa only [Pi.mul_apply, Matrix.one_mulVec, Real.norm_eq_abs,
      abs_mul, abs_of_nonneg (hnonneg x), norm_mul, Complex.norm_real,
      Real.norm_eq_abs, mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_left (hbound x) (abs_nonneg (x j))
  · intro j k
    apply (h2 j k).mono' (by unfold density quadratic Matrix.mulVec dotProduct; fun_prop)
    apply Filter.Eventually.of_forall
    intro x
    simpa only [Pi.mul_apply, Matrix.one_mulVec, Real.norm_eq_abs,
      abs_mul, abs_of_nonneg (hnonneg x), norm_mul, Complex.norm_real,
      Real.norm_eq_abs, mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_left (hbound x) (mul_nonneg (abs_nonneg (x j)) (abs_nonneg (x k)))

private lemma derivative_quadratic (A : Mat d) (x v : Vec d) :
    fderiv ℝ (quadratic A) x v = v ⬝ᵥ A.mulVec x + x ⬝ᵥ A.mulVec v := by
  have hq : quadratic A = fun y : Vec d => ∑ j, ∑ k, y j * A j k * y k := by
    funext y
    simp only [quadratic, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  rw [hq, fderiv_fun_sum (fun j _ => by fun_prop)]
  simp only [ContinuousLinearMap.sum_apply]
  have he (j : Fin d) :
      fderiv ℝ (fun y : Vec d => ∑ k, y j * A j k * y k) x v =
        ∑ k, (v j * A j k * x k + x j * A j k * v k) := by
    rw [fderiv_fun_sum (fun k _ => by fun_prop)]
    simp only [ContinuousLinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro k _
    rw [fderiv_fun_mul (by fun_prop) (by fun_prop), fderiv_mul_const (by fun_prop)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, (hasFDerivAt_apply (𝕜 := ℝ) j x).fderiv,
      (hasFDerivAt_apply (𝕜 := ℝ) k x).fderiv, ContinuousLinearMap.proj_apply]
    ring
  simp_rw [he]
  simp only [Matrix.mulVec, dotProduct, Finset.sum_add_distrib, Finset.mul_sum,
    mul_assoc]

private lemma derivative_linear (a x v : Vec d) :
    fderiv ℝ (fun y : Vec d => ((a ⬝ᵥ y : ℝ) : ℂ)) x v = (a ⬝ᵥ v : ℝ) := by
  change fderiv ℝ (fun y : Vec d => ((∑ j, a j * y j : ℝ) : ℂ)) x v = _
  simp only [Complex.ofReal_sum, Complex.ofReal_mul]
  rw [fderiv_fun_sum (fun j _ => by fun_prop)]
  simp only [ContinuousLinearMap.sum_apply, dotProduct, Complex.ofReal_sum, Complex.ofReal_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [fderiv_const_mul (by fun_prop)]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  change (a j : ℂ) * (fderiv ℝ (Complex.ofRealCLM ∘ fun y : Vec d => y j) x v) = _
  rw [fderiv_comp x Complex.ofRealCLM.differentiableAt (by fun_prop),
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.fderiv,
    (hasFDerivAt_apply (𝕜 := ℝ) j x).fderiv, ContinuousLinearMap.proj_apply]
  rfl

private lemma symmetric_dot (A : Mat d) (hA : A.transpose = A) (x y : Vec d) :
    x ⬝ᵥ A.mulVec y = y ⬝ᵥ A.mulVec x := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA, dotProduct_comm]

lemma derivative_density (A : Mat d) (hA : A.PosDef) (i j : Fin d) (z : ℂ)
    (x : Vec d) :
    fderiv ℝ (density A i z) x (A⁻¹.mulVec (unitVector j)) =
      (-(x j : ℂ) - Complex.I * z * (unitVector i j : ℂ)) * density A i z x := by
  let v := A⁻¹.mulVec (unitVector j)
  have hsym : A.transpose = A := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.isHermitian.eq
  have hAv : A.mulVec v = unitVector j := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A
      (isUnit_iff_ne_zero.mpr hA.det_pos.ne'), Matrix.one_mulVec]
  have hqd : fderiv ℝ (quadratic A) x v = 2 * x j := by
    rw [derivative_quadratic, symmetric_dot A hsym v x, hAv]
    simp [unitVector, dotProduct, Pi.single_apply, mul_ite]
    ring
  have hlin : A.mulVec (unitVector i) ⬝ᵥ v = unitVector i j := by
    rw [dotProduct_comm, symmetric_dot A hsym, hAv]
    simp [unitVector, dotProduct, Pi.single_apply, mul_ite]
  have hqdC : fderiv ℝ (fun y => (quadratic A y : ℂ)) x v = (2 * x j : ℝ) := by
    change fderiv ℝ (Complex.ofRealCLM ∘ quadratic A) x v = _
    rw [fderiv_comp x Complex.ofRealCLM.differentiableAt (by
      unfold quadratic Matrix.mulVec dotProduct; fun_prop),
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.fderiv, hqd]
    rfl
  unfold density
  have hdif : DifferentiableAt ℝ (fun y : Vec d =>
      -(quadratic A y : ℂ) / 2 - Complex.I * z *
        ((A.mulVec (unitVector i) ⬝ᵥ y : ℝ) : ℂ)) x := by
    unfold quadratic Matrix.mulVec dotProduct
    fun_prop
  rw [hdif.hasFDerivAt.cexp.fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  have heq : (fun y : Vec d => -(quadratic A y : ℂ) / 2) =
      fun y => (-1 / 2 : ℂ) * (quadratic A y : ℂ) := by funext y; ring
  rw [fderiv_fun_sub (by unfold quadratic Matrix.mulVec dotProduct; fun_prop)
    (by unfold Matrix.mulVec dotProduct; fun_prop), heq,
    fderiv_const_mul (by unfold quadratic Matrix.mulVec dotProduct; fun_prop),
    fderiv_const_mul (by unfold Matrix.mulVec dotProduct; fun_prop)]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [hqdC, derivative_linear, hlin]
  push_cast
  ring

/-- The determinant normalization is computed by whitening the actual matrix,
with the complex tilt retained for all complex force values. -/
lemma integral_density (A : Mat d) (hA : A.PosDef) (i : Fin d) (z : ℂ) :
    (∫ x : Vec d, density A i z x) =
      (((2 * Real.pi) ^ ((d : ℝ) / 2) / Real.sqrt A.det : ℝ) : ℂ) *
        Complex.exp (-((A i i / 2 : ℝ) : ℂ) * z ^ 2) := by
  let B := gaussianCovarianceSqrt A⁻¹
  let v := A.mulVec (unitVector i)
  let w := B.mulVec v
  have hAi : A⁻¹.PosDef := hA.inv
  have hB : B.PosDef := posDef_gaussianCovarianceSqrt A⁻¹ hAi
  have hBsym : B.transpose = B := transpose_gaussianCovarianceSqrt A⁻¹ hAi
  have hBsq : B * B = A⁻¹ := gaussianCovarianceSqrt_mul_self A⁻¹ hAi
  have hAunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hA.det_pos.ne'
  have hquad (x : Vec d) : quadratic A (B.mulVec x) = ∑ j, (x j) ^ 2 := by
    have h := quadratic_inv_mulVec_gaussianCovarianceSqrt A⁻¹ hAi x
    rw [Matrix.nonsing_inv_nonsing_inv A hAunit] at h
    simpa only [quadratic, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc] using h
  have hlin (x : Vec d) : v ⬝ᵥ B.mulVec x = w ⬝ᵥ x := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hBsym]
  have hw : (∑ j, (w j) ^ 2) = A i i := by
    have hsym : A.transpose = A := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.isHermitian.eq
    have hcalc : w ⬝ᵥ w = v ⬝ᵥ A⁻¹.mulVec v := by
      change B.mulVec v ⬝ᵥ B.mulVec v = _
      rw [dotProduct_comm, symmetric_dot B hBsym, Matrix.mulVec_mulVec, hBsq]
    have hv : A⁻¹.mulVec v = unitVector i := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hAunit, Matrix.one_mulVec]
    rw [show (∑ j, (w j) ^ 2) = w ⬝ᵥ w by simp only [dotProduct, pow_two], hcalc, hv]
    simp [v, unitVector, dotProduct, Pi.single_apply, mul_ite]
  have htrans (x : Vec d) : density A i z (B.mulVec x) =
      Complex.exp (-(1 / 2 : ℂ) * ∑ j, (x j : ℂ) ^ 2 +
        ∑ j, (-Complex.I * z * (w j : ℂ)) * (x j : ℂ)) := by
    rw [density, hquad, hlin]
    simp only [dotProduct, Complex.ofReal_sum, Complex.ofReal_pow, Complex.ofReal_mul]
    congr 1
    have hs : (∑ j, (-Complex.I * z * (w j : ℂ)) * (x j : ℂ)) =
        -Complex.I * z * ∑ j, (w j : ℂ) * (x j : ℂ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hs]
    ring
  have hprod := _root_.GaussianFourier.integral_cexp_neg_mul_sum_add
    (ι := Fin d) (b := (1 / 2 : ℂ)) (by norm_num) (fun j => -Complex.I * z * (w j : ℂ))
  have hsum : (∑ j, (-Complex.I * z * (w j : ℂ)) ^ 2) = -z ^ 2 * (A i i : ℂ) := by
    calc
      _ = -z ^ 2 * ∑ j, (w j : ℂ) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring_nf
        simp only [Complex.I_sq]
        ring
      _ = _ := by simp_rw [← Complex.ofReal_pow]; rw [← Complex.ofReal_sum, hw]
  have hJac := integral_comp_matrix_mulVec B hB.det_pos.ne' (density A i z)
  simp_rw [htrans] at hJac
  rw [hprod, hsum] at hJac
  have hpow : ((Real.pi : ℂ) / (1 / 2 : ℂ)) ^ ((Fintype.card (Fin d) : ℂ) / 2) =
      (((2 * Real.pi) ^ ((d : ℝ) / 2) : ℝ) : ℂ) := by
    rw [show (Real.pi : ℂ) / (1 / 2 : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by
      push_cast; ring, Fintype.card_fin]
    rw [show ((d : ℂ) / 2) = (((d : ℝ) / 2 : ℝ) : ℂ) by push_cast; rfl]
    exact (Complex.ofReal_cpow (by positivity) _).symm
  rw [hpow] at hJac
  have hdet : B.det = (Real.sqrt A.det)⁻¹ := by
    rw [det_gaussianCovarianceSqrt A⁻¹ hAi, Matrix.det_nonsing_inv, Ring.inverse_eq_inv,
      Real.sqrt_inv]
  have hdetpos := hB.det_pos
  rw [abs_of_pos hdetpos, Complex.real_smul] at hJac
  have he : -z ^ 2 * (A i i : ℂ) / (4 * (1 / 2)) =
      -((A i i / 2 : ℝ) : ℂ) * z ^ 2 := by push_cast; ring
  rw [he] at hJac
  apply mul_left_cancel₀ (show ((B.det⁻¹ : ℝ) : ℂ) ≠ 0 by exact_mod_cast inv_ne_zero hdetpos.ne')
  rw [← hJac, hdet]
  have hsqrt : (Real.sqrt A.det : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hA.det_pos).ne'
  push_cast
  field_simp

lemma integral_first_moment (A : Mat d) (hA : A.PosDef) (i j : Fin d) (z : ℂ) :
    (∫ x : Vec d, (x j : ℂ) * density A i z x) =
      -Complex.I * z * (unitVector i j : ℂ) * ∫ x : Vec d, density A i z x := by
  obtain ⟨h0, h1, _⟩ := integrable_moments A hA i z
  have hD : Integrable (fun x : Vec d =>
      fderiv ℝ (density A i z) x (A⁻¹.mulVec (unitVector j))) := by
    simp_rw [derivative_density A hA i j z, sub_mul, neg_mul]
    exact (h1 j).neg.sub (h0.const_mul _)
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure (Vec d)))
    (f := fun _ : Vec d => (1 : ℂ)) (g := density A i z)
    (v := A⁻¹.mulVec (unitVector j))
    (by simp only [fderiv_const_apply, ContinuousLinearMap.zero_apply, zero_mul]; exact integrable_zero (Vec d) ℂ _)
    (by simpa only [one_mul] using hD)
    (by simpa only [one_mul] using h0) (fun x _ => (differentiable_const _).differentiableAt)
    (by unfold density quadratic Matrix.mulVec dotProduct; fun_prop)
  simp only [one_mul, fderiv_const_apply, ContinuousLinearMap.zero_apply, zero_mul,
    integral_zero, neg_zero] at h
  simp_rw [derivative_density A hA i j z, sub_mul, neg_mul] at h
  have hlin : (∫ x : Vec d, -((x j : ℂ) * density A i z x) -
      (Complex.I * z * (unitVector i j : ℂ)) * density A i z x) =
      -(∫ x : Vec d, (x j : ℂ) * density A i z x) -
        (Complex.I * z * (unitVector i j : ℂ)) * ∫ x : Vec d, density A i z x := by
    simpa only [Pi.neg_apply, integral_neg, integral_const_mul] using
      integral_sub (h1 j).neg (h0.const_mul (Complex.I * z * (unitVector i j : ℂ)))
  rw [hlin] at h
  linear_combination -h

lemma integral_second_moment (A : Mat d) (hA : A.PosDef) (i j k : Fin d) (z : ℂ) :
    (∫ x : Vec d, (x j : ℂ) * (x k : ℂ) * density A i z x) =
      ((A⁻¹ j k : ℂ) - z ^ 2 * (unitVector i j : ℂ) * (unitVector i k : ℂ)) *
        ∫ x : Vec d, density A i z x := by
  obtain ⟨h0, h1, h2⟩ := integrable_moments A hA i z
  have hcoord (x v : Vec d) :
      fderiv ℝ (fun y : Vec d => (y j : ℂ)) x v = (v j : ℂ) := by
    change fderiv ℝ (Complex.ofRealCLM ∘ fun y : Vec d => y j) x v = _
    rw [fderiv_comp x Complex.ofRealCLM.differentiableAt (by fun_prop),
      ContinuousLinearMap.fderiv]
    simp only [ContinuousLinearMap.comp_apply, (hasFDerivAt_apply (𝕜 := ℝ) j x).fderiv,
      ContinuousLinearMap.proj_apply, Complex.ofRealCLM_apply]
  have hv : (A⁻¹.mulVec (unitVector k)) j = A⁻¹ j k := by
    simp [Matrix.mulVec, dotProduct, unitVector, Pi.single_apply, mul_ite]
  have hform (x : Vec d) : (x j : ℂ) *
      fderiv ℝ (density A i z) x (A⁻¹.mulVec (unitVector k)) =
        -((x j : ℂ) * (x k : ℂ) * density A i z x) -
          (Complex.I * z * (unitVector i k : ℂ)) * ((x j : ℂ) * density A i z x) := by
    rw [derivative_density A hA i k z]
    ring
  have hD : Integrable (fun x : Vec d => (x j : ℂ) *
      fderiv ℝ (density A i z) x (A⁻¹.mulVec (unitVector k))) := by
    simp_rw [hform]
    exact (h2 j k).neg.sub ((h1 j).const_mul _)
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure (Vec d)))
    (f := fun y : Vec d => (y j : ℂ)) (g := density A i z)
    (v := A⁻¹.mulVec (unitVector k))
    (by simp_rw [hcoord, hv]; exact h0.const_mul _) hD (h1 j)
    (by fun_prop) (by unfold density quadratic Matrix.mulVec dotProduct; fun_prop)
  simp_rw [hform, hcoord, hv] at h
  have hlin : (∫ x : Vec d, -((x j : ℂ) * (x k : ℂ) * density A i z x) -
      (Complex.I * z * (unitVector i k : ℂ)) * ((x j : ℂ) * density A i z x)) =
      -(∫ x : Vec d, (x j : ℂ) * (x k : ℂ) * density A i z x) -
        (Complex.I * z * (unitVector i k : ℂ)) *
          ∫ x : Vec d, (x j : ℂ) * density A i z x := by
    simpa only [Pi.neg_apply, integral_neg, integral_const_mul] using
      integral_sub (h2 j k).neg ((h1 j).const_mul (Complex.I * z * (unitVector i k : ℂ)))
  rw [hlin, integral_const_mul, integral_first_moment A hA i j z] at h
  calc
    _ = (A⁻¹ j k : ℂ) * (∫ x : Vec d, density A i z x) -
        (Complex.I * z * (unitVector i k : ℂ)) *
          (-Complex.I * z * (unitVector i j : ℂ) * ∫ x : Vec d, density A i z x) := by
      linear_combination -h
    _ = _ := by ring_nf; simp only [Complex.I_sq]; ring

lemma normalized_integral_density (A : Mat d) (hA : A.PosDef) (i : Fin d) (z : ℂ) :
    (((2 * Real.pi) ^ (-(d : ℝ)) : ℝ) : ℂ) * (∫ x : Vec d, density A i z x) =
      (((2 * Real.pi) ^ (-(d : ℝ) / 2) / Real.sqrt A.det : ℝ) : ℂ) *
        Complex.exp (-((A i i / 2 : ℝ) : ℂ) * z ^ 2) := by
  rw [integral_density A hA i z, ← mul_assoc, ← Complex.ofReal_mul]
  congr 1
  congr 1
  rw [← mul_div_assoc, ← Real.rpow_add (by positivity)]
  congr 2
  ring

lemma integral_linear_contraction (A : Mat d) (hA : A.PosDef) (i : Fin d) (z : ℂ)
    (C : Fin d → ℂ) :
    (∫ x : Vec d, density A i z x * ∑ j, (x j : ℂ) * C j) =
      -Complex.I * z * C i * ∫ x : Vec d, density A i z x := by
  have h1 := (integrable_moments A hA i z).2.1
  have he (x : Vec d) : density A i z x * ∑ j, (x j : ℂ) * C j =
      ∑ j, ((x j : ℂ) * density A i z x) * C j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [he]
  rw [integral_finset_sum _ (fun j _ => (h1 j).mul_const _)]
  simp_rw [integral_mul_const, integral_first_moment A hA i _ z]
  simp [unitVector, Pi.single_apply, apply_ite Complex.ofReal, mul_ite, ite_mul]
  ring

lemma integral_quadratic_contraction (A : Mat d) (hA : A.PosDef) (i : Fin d) (z : ℂ)
    (C : Matrix (Fin d) (Fin d) ℂ) :
    (∫ x : Vec d, density A i z x * ∑ j, ∑ k, (x j : ℂ) * (x k : ℂ) * C j k) =
      ((∑ j, ∑ k, (A⁻¹ j k : ℂ) * C j k) - z ^ 2 * C i i) *
        ∫ x : Vec d, density A i z x := by
  have h2 := (integrable_moments A hA i z).2.2
  have he (x : Vec d) : density A i z x * ∑ j, ∑ k, (x j : ℂ) * (x k : ℂ) * C j k =
      ∑ j, ∑ k, ((x j : ℂ) * (x k : ℂ) * density A i z x) * C j k := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp_rw [he]
  rw [integral_finsetSum (f := fun j x => ∑ k,
    ((x j : ℂ) * (x k : ℂ) * density A i z x) * C j k) _
    (fun j _ => integrable_finsetSum _ (fun k _ => (h2 j k).mul_const (C j k)))]
  simp_rw [integral_finsetSum (f := fun k x =>
    ((x _ : ℂ) * (x k : ℂ) * density A i z x) * C _ k) _
    (fun k _ => (h2 _ k).mul_const _), integral_mul_const,
    integral_second_moment A hA i _ _ z]
  have hsplit (j k : Fin d) :
      ((A⁻¹ j k : ℂ) - z ^ 2 * (unitVector i j : ℂ) * (unitVector i k : ℂ)) *
          (∫ x : Vec d, density A i z x) * C j k =
        ((A⁻¹ j k : ℂ) * C j k) * (∫ x : Vec d, density A i z x) -
          (z ^ 2 * (unitVector i j : ℂ) * (unitVector i k : ℂ) * C j k) *
            (∫ x : Vec d, density A i z x) := by ring
  simp_rw [hsplit, Finset.sum_sub_distrib, ← Finset.sum_mul]
  simp [unitVector, Pi.single_apply, apply_ite Complex.ofReal, mul_ite, ite_mul]
  ring

lemma velocity_fourier_contraction (A : Mat d) (hA : A.PosDef) (i : Fin d) (z : ℂ)
    (C : Matrix (Fin d) (Fin d) ℂ) :
    let N : ℂ := (((2 * Real.pi) ^ (-(d : ℝ)) : ℝ) : ℂ)
    N * (∫ x : Vec d, density A i z x *
        ((1 / 4 : ℂ) * ∑ j, ∑ k, (x j : ℂ) * (x k : ℂ) * C j k)) +
      N * (∫ x : Vec d, density A i z x *
        ((1 / 2 : ℂ) * Complex.I * z * ∑ j, (x j : ℂ) * C j i)) =
      (1 / 4 : ℂ) * (((2 * Real.pi) ^ (-(d : ℝ) / 2) / Real.sqrt A.det : ℝ) : ℂ) *
        ((∑ j, ∑ k, (A⁻¹ j k : ℂ) * C j k) + C i i * z ^ 2) *
          Complex.exp (-((A i i / 2 : ℝ) : ℂ) * z ^ 2) := by
  dsimp only
  simp_rw [mul_left_comm (density A i z _) (1 / 4 : ℂ),
    mul_left_comm (density A i z _) ((1 / 2 : ℂ) * Complex.I * z),
    integral_const_mul, integral_quadratic_contraction A hA i z C,
    integral_linear_contraction A hA i z (fun j => C j i)]
  have hn := normalized_integral_density A hA i z
  calc
    _ = (1 / 4 : ℂ) *
        ((∑ j, ∑ k, (A⁻¹ j k : ℂ) * C j k) + C i i * z ^ 2) *
          ((((2 * Real.pi) ^ (-(d : ℝ)) : ℝ) : ℂ) * ∫ x : Vec d, density A i z x) := by
      ring_nf
      simp only [Complex.I_sq]
      ring
    _ = _ := by rw [hn]; ring

lemma clock_fourier_contraction (A : Mat d) (hA : A.PosDef) (i : Fin d) (z : ℂ)
    (C : Fin d → ℂ) :
    (((2 * Real.pi) ^ (-(d : ℝ)) : ℝ) : ℂ) * (z / 2) *
      (∫ x : Vec d, density A i z x * (Complex.I * ∑ j, (x j : ℂ) * C j)) =
      (1 / 2 : ℂ) * (((2 * Real.pi) ^ (-(d : ℝ) / 2) / Real.sqrt A.det : ℝ) : ℂ) *
        C i * z ^ 2 * Complex.exp (-((A i i / 2 : ℝ) : ℂ) * z ^ 2) := by
  simp_rw [mul_left_comm (density A i z _) Complex.I,
    integral_const_mul, integral_linear_contraction A hA i z C]
  have hn := normalized_integral_density A hA i z
  calc
    _ = (1 / 2 : ℂ) * C i * z ^ 2 *
        ((((2 * Real.pi) ^ (-(d : ℝ)) : ℝ) : ℂ) * ∫ x : Vec d, density A i z x) := by
      ring_nf
      simp only [Complex.I_sq]
      ring
    _ = _ := by rw [hn]; ring

end EinsteinFull.Blueprint.GaussianFourier
