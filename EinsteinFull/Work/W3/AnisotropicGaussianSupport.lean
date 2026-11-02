import EinsteinFull.Frozen.ClockGaussianProfile
import EinsteinRelation.Correctors.HomogenizedMatrixBounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic

/-!
# Anisotropic Gaussian derivatives and profile contractions

The real density has covariance `s A`, so the density `p_A` in
`paper/main.tex:1258–1280` is the frozen unforced kernel at time `s = 1`.
The generator in that definition already contains `1/2`; no additional time
conversion or factor of two occurs. All spatial derivatives use `Fin d → ℝ`
and the coordinate directions `unitVector`; no function-space norm substitutes
for Euclidean geometry. The final contractions are deterministic identities
on the actual frozen profiles and do not assert a stochastic scaling limit.
-/

namespace EinsteinFull

open EinsteinRelation
open scoped BigOperators

variable {d : ℕ}

private lemma fderiv_quadratic (B : Mat d) (x v : Vec d) :
    fderiv ℝ (fun y : Vec d => ∑ j, ∑ k, y j * B j k * y k) x v =
      ∑ j, ∑ k, (v j * B j k * x k + x j * B j k * v k) := by
  rw [fderiv_fun_sum (fun j _ => by fun_prop)]
  simp only [ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [fderiv_fun_sum (fun k _ => by fun_prop)]
  simp only [ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [fderiv_fun_mul (by fun_prop) (by fun_prop),
    fderiv_mul_const (by fun_prop)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, (hasFDerivAt_apply (𝕜 := ℝ) j x).fderiv, (hasFDerivAt_apply (𝕜 := ℝ) k x).fderiv,
    ContinuousLinearMap.proj_apply]
  ring

private lemma fderiv_quadratic_coordinate (B : Mat d) (hB : B.transpose = B) (x : Vec d) (j : Fin d) :
    fderiv ℝ (fun y : Vec d => ∑ a, ∑ b, y a * B a b * y b) x (unitVector j) =
      2 * (B.mulVec x) j := by
  rw [fderiv_quadratic]
  have hs (a b : Fin d) : B b a = B a b := congrFun (congrFun hB a) b
  simp only [unitVector, Pi.single_apply, ite_mul, mul_ite, zero_mul, mul_zero,
    one_mul, mul_one, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, hs]
  rw [Finset.sum_comm (f := fun a b => if a = j then B a b * x b else 0)]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  change (∑ b, B j b * x b) + (∑ a, x a * B j a) = 2 * ∑ b, B j b * x b
  simp only [mul_comm (x _) (B j _)]
  ring

/-- Real density with covariance `s • A`, retaining the determinant and inverse. -/
noncomputable def anisotropicGaussian (A : Mat d) (s : ℝ) (x : Vec d) : ℝ :=
  (2 * Real.pi * s) ^ (-(d : ℝ) / 2) / Real.sqrt A.det *
    Real.exp (-(∑ j, ∑ k, x j * (A⁻¹) j k * x k) / (2 * s))

/-- The literal anisotropic density is smooth in its spatial coordinates. -/
theorem contDiff_anisotropicGaussian (A : Mat d) (s : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (anisotropicGaussian A s) := by
  unfold anisotropicGaussian
  fun_prop

/-- First spatial coordinate derivative, with the actual matrix inverse. -/
theorem fderiv_anisotropicGaussian_coordinate (A : Mat d) (hA : A.transpose = A)
    (s : ℝ) (x : Vec d) (j : Fin d) :
    fderiv ℝ (anisotropicGaussian A s) x (unitVector j) =
      -((A⁻¹).mulVec x) j / s * anisotropicGaussian A s x := by
  have hB : (A⁻¹).transpose = A⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hA]
  unfold anisotropicGaussian
  rw [fderiv_const_mul (by fun_prop), fderiv_exp (by fun_prop)]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [show (fun y : Vec d => -(∑ a, ∑ b, y a * (A⁻¹) a b * y b) / (2 * s)) =
    (fun y => (-1 / (2 * s)) * (∑ a, ∑ b, y a * (A⁻¹) a b * y b)) by
      funext y; ring]
  rw [fderiv_const_mul (by fun_prop)]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [fderiv_quadratic_coordinate _ hB]
  ring

private lemma fderiv_mulVec_coordinate (B : Mat d) (x : Vec d) (j k : Fin d) :
    fderiv ℝ (fun y => B.mulVec y j) x (unitVector k) = B j k := by
  change fderiv ℝ (fun y : Vec d => ∑ a, B j a * y a) x (unitVector k) = _
  rw [fderiv_fun_sum (fun a _ => by fun_prop)]
  simp only [ContinuousLinearMap.sum_apply]
  calc
    _ = ∑ a, B j a * unitVector k a := by
      apply Finset.sum_congr rfl
      intro a _
      rw [fderiv_const_mul (by fun_prop)]
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul,
        (hasFDerivAt_apply (𝕜 := ℝ) a x).fderiv, ContinuousLinearMap.proj_apply]
    _ = _ := by simp [unitVector, Pi.single_apply, mul_ite]

private lemma differentiableAt_mulVec_coordinate (B : Mat d) (x : Vec d) (j : Fin d) :
    DifferentiableAt ℝ (fun y => B.mulVec y j) x := by
  change DifferentiableAt ℝ (fun y : Vec d => ∑ a, B j a * y a) x
  fun_prop

/-- Second spatial coordinate derivative, including the anisotropic inverse term. -/
theorem fderiv_fderiv_anisotropicGaussian_coordinate
    (A : Mat d) (hA : A.transpose = A) (s : ℝ) (x : Vec d) (j k : Fin d) :
    fderiv ℝ (fun y => fderiv ℝ (anisotropicGaussian A s) y (unitVector j))
        x (unitVector k) =
      (((A⁻¹).mulVec x j * (A⁻¹).mulVec x k) / s ^ 2 - (A⁻¹) j k / s) *
        anisotropicGaussian A s x := by
  simp_rw [fderiv_anisotropicGaussian_coordinate A hA]
  have heq : (fun y : Vec d => -((A⁻¹).mulVec y) j / s * anisotropicGaussian A s y) =
      fun y => (-1 / s) * ((A⁻¹).mulVec y j * anisotropicGaussian A s y) := by
    funext y; ring
  rw [heq, fderiv_const_mul (by
    exact (differentiableAt_mulVec_coordinate (A⁻¹) x j).mul
      ((contDiff_anisotropicGaussian A s).differentiable (by simp)).differentiableAt),
    fderiv_fun_mul (differentiableAt_mulVec_coordinate (A⁻¹) x j)
      ((contDiff_anisotropicGaussian A s).differentiable (by simp)).differentiableAt]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, smul_eq_mul]
  rw [fderiv_mulVec_coordinate, fderiv_anisotropicGaussian_coordinate A hA]
  ring

/-- Inverse cancellation at the anisotropic force displacement. -/
theorem inv_mulVec_gaussianShift (A : Mat d) (hdet : IsUnit A.det) (i : Fin d) (z : ℝ) :
    (A⁻¹).mulVec ((-z) • A.mulVec (unitVector i)) = (-z) • unitVector i := by
  rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hdet,
    Matrix.one_mulVec]

/-- The anisotropic quadratic form at the force displacement. -/
theorem quadratic_gaussianShift (A : Mat d) (hdet : IsUnit A.det) (i : Fin d) (z : ℝ) :
    (∑ j, ∑ k, ((-z) • A.mulVec (unitVector i)) j * (A⁻¹) j k *
      ((-z) • A.mulVec (unitVector i)) k) = z ^ 2 * A i i := by
  have hq (x : Vec d) : (∑ j, ∑ k, x j * (A⁻¹) j k * x k) =
      ∑ j, x j * (A⁻¹).mulVec x j := by
    apply Finset.sum_congr rfl
    intro j _
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  rw [hq, inv_mulVec_gaussianShift A hdet]
  simp [Pi.smul_apply, smul_eq_mul, unitVector, Pi.single_apply, mul_ite]
  ring

/-- Covariance `A` occurs at time one, with the manuscript's exact prefactor. -/
theorem anisotropicGaussian_gaussianShift (A : Mat d) (hdet : IsUnit A.det)
    (i : Fin d) (z : ℝ) :
    anisotropicGaussian A 1 ((-z) • A.mulVec (unitVector i)) =
      ((2 * Real.pi) ^ (-(d : ℝ) / 2) / Real.sqrt A.det) *
        Real.exp (-(A i i / 2) * z ^ 2) := by
  unfold anisotropicGaussian
  rw [quadratic_gaussianShift A hdet]
  congr 1
  · rw [mul_one]
  · congr 1
    ring

/-- First derivative at `-z A e_i`, for real signed force. -/
theorem fderiv_anisotropicGaussian_gaussianShift (A : Mat d) (hA : A.transpose = A)
    (hdet : IsUnit A.det) (i j : Fin d) (z : ℝ) :
    fderiv ℝ (anisotropicGaussian A 1) ((-z) • A.mulVec (unitVector i)) (unitVector j) =
      z * unitVector i j * anisotropicGaussian A 1 ((-z) • A.mulVec (unitVector i)) := by
  rw [fderiv_anisotropicGaussian_coordinate A hA, inv_mulVec_gaussianShift A hdet]
  simp only [Pi.smul_apply, smul_eq_mul, div_one]
  ring

/-- The negative Hessian at `-z A e_i`, as in the Fourier calculation. -/
theorem neg_fderiv_fderiv_anisotropicGaussian_gaussianShift
    (A : Mat d) (hA : A.transpose = A) (hdet : IsUnit A.det) (i j k : Fin d) (z : ℝ) :
    -fderiv ℝ (fun y => fderiv ℝ (anisotropicGaussian A 1) y (unitVector j))
        ((-z) • A.mulVec (unitVector i)) (unitVector k) =
      ((A⁻¹) j k - z ^ 2 * unitVector i j * unitVector i k) *
        anisotropicGaussian A 1 ((-z) • A.mulVec (unitVector i)) := by
  rw [fderiv_fderiv_anisotropicGaussian_coordinate A hA, inv_mulVec_gaussianShift A hdet]
  simp only [Pi.smul_apply, smul_eq_mul, one_pow, div_one]
  ring

/-- The actual variational homogenized coefficient is positive definite. -/
theorem posDef_homogenizedCoefficient {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) :
    (homogenizedCoefficient Q).PosDef := by
  change (homogenizedMatrix Q).PosDef
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  refine ⟨?_, fun x hx => ?_⟩
  · simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using
      homogenizedMatrix_transpose Q
  · have hL : 0 < sourceReducedBound Λ₀ := by
      unfold sourceReducedBound
      apply mul_pos (Real.exp_pos _)
      nlinarith [Q.ellipticity_parameter, sq_nonneg Λ₀]
    have hsq : 0 < euclideanSq x := by
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hx
      have hj' : x j ≠ 0 := hj
      exact (mul_self_pos.mpr hj').trans_le
        (Finset.single_le_sum (fun k _ => mul_self_nonneg (x k)) (Finset.mem_univ j))
    have h := (mul_pos (inv_pos.mpr hL) hsq).trans_le
      (homogenizedMatrix_quadratic_lower Q x)
    simpa only [star_trivial] using! h

/-- In particular the actual determinant in the Gaussian normalization is positive. -/
theorem det_homogenizedCoefficient_pos {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) :
    0 < (homogenizedCoefficient Q).det := (posDef_homogenizedCoefficient Q).det_pos

/-- At zero force the frozen complex kernel is the embedding of the real density. -/
theorem homogenizedGaussianKernel_zero_eq_ofReal {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (s : ℝ) (hs : 0 < s) (x : Vec d) :
    homogenizedGaussianKernel Q i s hs 0 x =
      (anisotropicGaussian (homogenizedCoefficient Q) s x : ℂ) := by
  simp only [homogenizedGaussianKernel, anisotropicGaussian, zero_mul, sub_zero,
    Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_neg,
    Complex.ofReal_sum, Complex.ofReal_ofNat]

/-- Real force translates the literal frozen kernel by `z s A e_i`. -/
theorem homogenizedGaussianKernel_realForce_eq_translate {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (s : ℝ) (hs : 0 < s) (z : ℝ) (x : Vec d) :
    homogenizedGaussianKernel Q i s hs (z : ℂ) x =
      homogenizedGaussianKernel Q i s hs 0
        (x - (z * s) • (homogenizedCoefficient Q).mulVec (unitVector i)) := by
  simp only [homogenizedGaussianKernel, zero_mul, sub_zero, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, Complex.ofReal_sub, Complex.ofReal_mul]

private lemma fderiv_ofReal_apply (f : Vec d → ℝ) (x v : Vec d)
    (hf : DifferentiableAt ℝ f x) :
    fderiv ℝ (fun y => (f y : ℂ)) x v = (fderiv ℝ f x v : ℂ) := by
  change fderiv ℝ (Complex.ofRealCLM ∘ f) x v = _
  rw [fderiv_comp x Complex.ofRealCLM.differentiableAt hf,
    ContinuousLinearMap.fderiv]
  rfl

/-- First spatial derivative of the frozen kernel at zero force and arbitrary time. -/
theorem fderiv_homogenizedGaussianKernel_zero_coordinate {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i j : Fin d) (s : ℝ) (hs : 0 < s) (x : Vec d) :
    fderiv ℝ (homogenizedGaussianKernel Q i s hs 0) x (unitVector j) =
      ((-((homogenizedCoefficient Q)⁻¹).mulVec x j / s : ℝ) : ℂ) *
        homogenizedGaussianKernel Q i s hs 0 x := by
  have hA : (homogenizedCoefficient Q).transpose = homogenizedCoefficient Q :=
    homogenizedMatrix_transpose Q
  have hf := (contDiff_anisotropicGaussian (homogenizedCoefficient Q) s).differentiable
    (by simp)
  have hK : homogenizedGaussianKernel Q i s hs 0 =
      fun y => (anisotropicGaussian (homogenizedCoefficient Q) s y : ℂ) :=
    funext (homogenizedGaussianKernel_zero_eq_ofReal Q i s hs)
  rw [hK]
  rw [fderiv_ofReal_apply _ _ _ hf.differentiableAt,
    fderiv_anisotropicGaussian_coordinate _ hA]
  rw [Complex.ofReal_mul]

/-- Second spatial derivative of the same frozen kernel, with covariance `s A`. -/
theorem fderiv_fderiv_homogenizedGaussianKernel_zero_coordinate {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i j k : Fin d) (s : ℝ) (hs : 0 < s) (x : Vec d) :
    fderiv ℝ (fun y => fderiv ℝ (homogenizedGaussianKernel Q i s hs 0) y (unitVector j))
        x (unitVector k) =
      (((((homogenizedCoefficient Q)⁻¹).mulVec x j *
          ((homogenizedCoefficient Q)⁻¹).mulVec x k) / s ^ 2 -
        ((homogenizedCoefficient Q)⁻¹) j k / s : ℝ) : ℂ) *
          homogenizedGaussianKernel Q i s hs 0 x := by
  have hA : (homogenizedCoefficient Q).transpose = homogenizedCoefficient Q :=
    homogenizedMatrix_transpose Q
  have hf (y : Vec d) :=
    ((contDiff_anisotropicGaussian (homogenizedCoefficient Q) s).differentiable
      (by simp)).differentiableAt (x := y)
  have hdf : DifferentiableAt ℝ (fun y =>
      fderiv ℝ (anisotropicGaussian (homogenizedCoefficient Q) s) y (unitVector j)) x := by
    simp_rw [fderiv_anisotropicGaussian_coordinate _ hA]
    have hg : DifferentiableAt ℝ (fun y : Vec d =>
        -((homogenizedCoefficient Q)⁻¹).mulVec y j / s) x := by
      unfold Matrix.mulVec dotProduct
      fun_prop
    exact hg.mul (hf x)
  have hK : homogenizedGaussianKernel Q i s hs 0 =
      fun y => (anisotropicGaussian (homogenizedCoefficient Q) s y : ℂ) :=
    funext (homogenizedGaussianKernel_zero_eq_ofReal Q i s hs)
  rw [hK]
  simp_rw [fderiv_ofReal_apply _ _ _ (hf _)]
  rw [fderiv_ofReal_apply _ _ _ hdf,
    fderiv_fderiv_anisotropicGaussian_coordinate _ hA, Complex.ofReal_mul]

/-- The manuscript's `p_A(-z A e_i)` is the actual frozen time-one kernel. -/
theorem homogenizedGaussianKernel_gaussianShift {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (z : ℝ) :
    homogenizedGaussianKernel Q i 1 (by norm_num) 0
        ((-z) • (homogenizedCoefficient Q).mulVec (unitVector i)) =
      ((((2 * Real.pi) ^ (-(d : ℝ) / 2) /
        Real.sqrt (homogenizedCoefficient Q).det) : ℝ) : ℂ) *
          Complex.exp (-((homogenizedCoefficient Q i i / 2 : ℝ) : ℂ) * (z : ℂ) ^ 2) := by
  rw [homogenizedGaussianKernel_zero_eq_ofReal,
    anisotropicGaussian_gaussianShift _ (isUnit_iff_ne_zero.mpr
      (det_homogenizedCoefficient_pos Q).ne')]
  simp only [Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_pow]

/-- The first manuscript derivative identity on the actual homogenized kernel. -/
theorem fderiv_homogenizedGaussianKernel_gaussianShift {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i j : Fin d) (z : ℝ) :
    fderiv ℝ (homogenizedGaussianKernel Q i 1 (by norm_num) 0)
        ((-z) • (homogenizedCoefficient Q).mulVec (unitVector i)) (unitVector j) =
      ((z * unitVector i j : ℝ) : ℂ) *
        homogenizedGaussianKernel Q i 1 (by norm_num) 0
          ((-z) • (homogenizedCoefficient Q).mulVec (unitVector i)) := by
  rw [fderiv_homogenizedGaussianKernel_zero_coordinate,
    inv_mulVec_gaussianShift _ (isUnit_iff_ne_zero.mpr
      (det_homogenizedCoefficient_pos Q).ne')]
  simp only [Pi.smul_apply, smul_eq_mul, div_one, neg_mul, neg_neg]

/-- The negative Hessian identity on the actual homogenized kernel. -/
theorem neg_fderiv_fderiv_homogenizedGaussianKernel_gaussianShift {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i j k : Fin d) (z : ℝ) :
    -fderiv ℝ (fun y => fderiv ℝ (homogenizedGaussianKernel Q i 1 (by norm_num) 0)
        y (unitVector j))
        ((-z) • (homogenizedCoefficient Q).mulVec (unitVector i)) (unitVector k) =
      ((((homogenizedCoefficient Q)⁻¹) j k - z ^ 2 * unitVector i j * unitVector i k : ℝ) : ℂ) *
        homogenizedGaussianKernel Q i 1 (by norm_num) 0
          ((-z) • (homogenizedCoefficient Q).mulVec (unitVector i)) := by
  rw [fderiv_fderiv_homogenizedGaussianKernel_zero_coordinate,
    inv_mulVec_gaussianShift _ (isUnit_iff_ne_zero.mpr
      (det_homogenizedCoefficient_pos Q).ne')]
  simp only [Pi.smul_apply, smul_eq_mul, one_pow, div_one]
  rw [← neg_mul, ← Complex.ofReal_neg]
  congr 2
  ring

private lemma gaussian_velocity_contraction_algebra (B C : Matrix (Fin d) (Fin d) ℂ)
    (i : Fin d) (z p : ℂ) :
    (1 / 4 : ℂ) * (∑ j, ∑ k,
      (B j k - z ^ 2 * (unitVector i j : ℂ) * (unitVector i k : ℂ)) * p * C j k) +
      z / 2 * (∑ j, (z * (unitVector i j : ℂ) * p) * C j i) =
    (1 / 4 : ℂ) * p * ((∑ j, ∑ k, B j k * C j k) + C i i * z ^ 2) := by
  have hB : (∑ j, ∑ k, B j k * p * C j k) = (∑ j, ∑ k, B j k * C j k) * p := by
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hC : (∑ j, ∑ k,
      z ^ 2 * (unitVector i j : ℂ) * (unitVector i k : ℂ) * p * C j k) =
        z ^ 2 * p * C i i := by
    simp [unitVector, Pi.single_apply, apply_ite Complex.ofReal, ite_mul, mul_ite]
  have hF : (∑ j, (z * (unitVector i j : ℂ) * p) * C j i) = z * p * C i i := by
    simp [unitVector, Pi.single_apply, apply_ite Complex.ofReal, ite_mul, mul_ite]
  simp_rw [sub_mul, Finset.sum_sub_distrib]
  rw [hB, hC, hF]
  ring

/-- The two divergence and force contractions give exactly the frozen velocity
profile, for real force and the actual homogenized kernel. No random limit is used. -/
theorem velocityGaussianProfile_eq_kernel_contraction {Λ₀ r₀ : ℝ} (hd : 2 ≤ d)
    (Q : EnvironmentLaw d Λ₀ r₀)
    (covariance : Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ)
    (i : Fin d) (z : ℝ) :
    let first : Fin d := ⟨0, by omega⟩
    let h := (-z) • (homogenizedCoefficient Q).mulVec (unitVector first)
    let p := homogenizedGaussianKernel Q first 1 (by norm_num) 0
    (1 / 4 : ℂ) * (∑ j, ∑ k,
      (-fderiv ℝ (fun y => fderiv ℝ p y (unitVector j)) h (unitVector k)) *
        (covariance (.inl (j, first)) (.inl (k, i)) : ℂ)) +
      (z : ℂ) / 2 * (∑ j, fderiv ℝ p h (unitVector j) *
        (covariance (.inl (j, first)) (.inl (first, i)) : ℂ)) =
      velocityGaussianProfile hd Q covariance i (z : ℂ) := by
  dsimp only
  simp_rw [neg_fderiv_fderiv_homogenizedGaussianKernel_gaussianShift,
    fderiv_homogenizedGaussianKernel_gaussianShift]
  simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_pow]
  erw [gaussian_velocity_contraction_algebra
    (fun j k => ((homogenizedCoefficient Q)⁻¹ j k : ℂ))
    (fun j k => (covariance (.inl (j, ⟨0, by omega⟩)) (.inl (k, i)) : ℂ))
    (⟨0, by omega⟩ : Fin d) (z : ℂ),
    homogenizedGaussianKernel_gaussianShift]
  unfold velocityGaussianProfile
  simp only [Complex.ofReal_sum, Complex.ofReal_mul]
  ring

/-- The commutator-clock contraction gives exactly the frozen clock profile. -/
theorem clockGaussianProfile_eq_kernel_contraction {Λ₀ r₀ : ℝ} (hd : 2 ≤ d)
    (Q : EnvironmentLaw d Λ₀ r₀)
    (covariance : Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ) (z : ℝ) :
    let first : Fin d := ⟨0, by omega⟩
    let h := (-z) • (homogenizedCoefficient Q).mulVec (unitVector first)
    let p := homogenizedGaussianKernel Q first 1 (by norm_num) 0
    (z : ℂ) / 2 * (∑ j, fderiv ℝ p h (unitVector j) *
      (covariance (.inl (j, first)) (.inr ()) : ℂ)) =
        clockGaussianProfile hd Q covariance (z : ℂ) := by
  dsimp only
  simp_rw [fderiv_homogenizedGaussianKernel_gaussianShift]
  simp only [Complex.ofReal_mul]
  simp only [unitVector, Pi.single_apply, apply_ite Complex.ofReal, Complex.ofReal_one,
    Complex.ofReal_zero, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hp := homogenizedGaussianKernel_gaussianShift Q ⟨0, by omega⟩ z
  simp only [unitVector] at hp
  rw [hp]
  unfold clockGaussianProfile
  ring

end EinsteinFull
