import EinsteinFull.Work.W3.AnisotropicGaussianSupport

/-!
# Complex-force Gaussian spatial derivatives and deterministic profiles

Direct real spatial differentiation of the literal frozen exponential proves the
complex extension in `paper/main.tex:1260–1280`. At time one, its value at real
`x = 0` represents `p_A(-ζ A e_i)`, without a complex spatial carrier. All
contractions below concern the actual frozen profiles, with covariance `s A`.
-/

namespace EinsteinFull

open EinsteinRelation
open scoped BigOperators

variable {d : ℕ}

@[fun_prop] private lemma differentiableAt_complexOfReal (x : ℝ) :
    DifferentiableAt ℝ (fun t : ℝ => (t : ℂ)) x :=
  Complex.ofRealCLM.differentiableAt

@[fun_prop] private lemma contDiff_complexOfReal (n : WithTop ℕ∞) :
    ContDiff ℝ n (fun t : ℝ => (t : ℂ)) := Complex.ofRealCLM.contDiff

private lemma fderiv_complex_coordinate (x v : Vec d) (j : Fin d) :
    fderiv ℝ (fun y : Vec d => (y j : ℂ)) x v = (v j : ℂ) := by
  change fderiv ℝ (Complex.ofRealCLM ∘ fun y : Vec d => y j) x v = _
  rw [fderiv_comp x Complex.ofRealCLM.differentiableAt (by fun_prop),
    ContinuousLinearMap.fderiv]
  simp only [ContinuousLinearMap.comp_apply, (hasFDerivAt_apply (𝕜 := ℝ) j x).fderiv,
    ContinuousLinearMap.proj_apply, Complex.ofRealCLM_apply]

private lemma fderiv_complex_exp {f : Vec d → ℂ} {x : Vec d}
    (hf : DifferentiableAt ℝ f x) :
    fderiv ℝ (fun y => Complex.exp (f y)) x = Complex.exp (f x) • fderiv ℝ f x :=
  hf.hasFDerivAt.cexp.fderiv

private lemma fderiv_shifted_quadratic_coordinate (B : Mat d) (hB : B.transpose = B)
    (c : Fin d → ℂ) (x : Vec d) (j : Fin d) :
    fderiv ℝ (fun y : Vec d => ∑ a, ∑ b,
      ((y a : ℂ) - c a) * (B a b : ℂ) * ((y b : ℂ) - c b)) x (unitVector j) =
      2 * ∑ b, (B j b : ℂ) * ((x b : ℂ) - c b) := by
  rw [fderiv_fun_sum (fun a _ => by fun_prop)]
  simp only [ContinuousLinearMap.sum_apply]
  have hd (a b : Fin d) :
      fderiv ℝ (fun y : Vec d =>
        ((y a : ℂ) - c a) * (B a b : ℂ) * ((y b : ℂ) - c b)) x (unitVector j) =
      (unitVector j a : ℂ) * (B a b : ℂ) * ((x b : ℂ) - c b) +
        ((x a : ℂ) - c a) * (B a b : ℂ) * (unitVector j b : ℂ) := by
    rw [fderiv_fun_mul (by fun_prop) (by fun_prop), fderiv_mul_const (by fun_prop)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, fderiv_sub_const, fderiv_complex_coordinate]
    ring
  have hdSum (a : Fin d) := fderiv_fun_sum (𝕜 := ℝ) (x := x)
    (u := Finset.univ) (A := fun b y =>
      ((y a : ℂ) - c a) * (B a b : ℂ) * ((y b : ℂ) - c b))
    (fun b _ => by fun_prop)
  simp_rw [hdSum, ContinuousLinearMap.sum_apply, hd]
  have hs (a b : Fin d) : B b a = B a b := congrFun (congrFun hB a) b
  simp only [unitVector, Pi.single_apply, apply_ite Complex.ofReal, Complex.ofReal_one,
    Complex.ofReal_zero, ite_mul, mul_ite, zero_mul, mul_zero, one_mul, mul_one,
    Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, hs]
  rw [Finset.sum_comm (f := fun a b =>
    if a = j then (B a b : ℂ) * ((x b : ℂ) - c b) else 0)]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [mul_comm ((x _ : ℂ) - c _) (B j _ : ℂ)]
  ring

private lemma inverse_shift_sum {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (i j : Fin d) (s : ℝ) (ζ : ℂ) (x : Vec d) :
    (∑ k, (((homogenizedCoefficient Q)⁻¹) j k : ℂ) *
      ((x k : ℂ) - ζ * (s : ℂ) * ((homogenizedCoefficient Q).mulVec (unitVector i) k : ℂ))) =
      (((homogenizedCoefficient Q)⁻¹).mulVec x j : ℂ) -
        ζ * (s : ℂ) * (unitVector i j : ℂ) := by
  have hi : ((homogenizedCoefficient Q)⁻¹).mulVec
      ((homogenizedCoefficient Q).mulVec (unitVector i)) = unitVector i := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _
      (isUnit_iff_ne_zero.mpr (det_homogenizedCoefficient_pos Q).ne'), Matrix.one_mulVec]
  have his := congrArg (fun v : Vec d => (v j : ℂ)) hi
  change ((∑ k, ((homogenizedCoefficient Q)⁻¹) j k *
    (homogenizedCoefficient Q).mulVec (unitVector i) k : ℝ) : ℂ) = _ at his
  simp only [Complex.ofReal_sum, Complex.ofReal_mul] at his
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [show (∑ k, (((homogenizedCoefficient Q)⁻¹) j k : ℂ) *
      (ζ * (s : ℂ) * ((homogenizedCoefficient Q).mulVec (unitVector i) k : ℂ))) =
      ζ * (s : ℂ) * (∑ k, (((homogenizedCoefficient Q)⁻¹) j k : ℂ) *
        ((homogenizedCoefficient Q).mulVec (unitVector i) k : ℂ)) by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring]
  rw [his]
  simp only [Matrix.mulVec, dotProduct, Complex.ofReal_sum, Complex.ofReal_mul]

/-- Smoothness in the full real spatial variable for every complex force. -/
theorem contDiff_homogenizedGaussianKernel_complexForce {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (s : ℝ) (hs : 0 < s) (ζ : ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (homogenizedGaussianKernel Q i s hs ζ) := by
  unfold homogenizedGaussianKernel
  fun_prop

/-- First real spatial Fréchet derivative in each Euclidean coordinate direction. -/
theorem fderiv_homogenizedGaussianKernel_complexForce_coordinate {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i j : Fin d) (s : ℝ) (hs : 0 < s) (ζ : ℂ) (x : Vec d) :
    fderiv ℝ (homogenizedGaussianKernel Q i s hs ζ) x (unitVector j) =
      (ζ * (unitVector i j : ℂ) -
        (((homogenizedCoefficient Q)⁻¹).mulVec x j : ℂ) / (s : ℂ)) *
          homogenizedGaussianKernel Q i s hs ζ x := by
  have hB : ((homogenizedCoefficient Q)⁻¹).transpose = (homogenizedCoefficient Q)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv]
    change (Matrix.transpose (homogenizedMatrix Q))⁻¹ = _
    rw [homogenizedMatrix_transpose Q]
    rfl
  unfold homogenizedGaussianKernel
  rw [fderiv_const_mul (by fun_prop), fderiv_complex_exp (by fun_prop)]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  simp_rw [div_eq_mul_inv]
  rw [fderiv_mul_const (by fun_prop), fderiv_fun_neg]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, ContinuousLinearMap.neg_apply]
  rw [fderiv_shifted_quadratic_coordinate _ hB]
  rw [inverse_shift_sum]
  have hsC : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  field_simp
  ring

private lemma fderiv_complex_mulVec_coordinate (B : Mat d) (x : Vec d) (j k : Fin d) :
    fderiv ℝ (fun y : Vec d => (B.mulVec y j : ℂ)) x (unitVector k) = (B j k : ℂ) := by
  change fderiv ℝ (fun y : Vec d => ((∑ a, B j a * y a : ℝ) : ℂ)) x (unitVector k) = _
  simp only [Complex.ofReal_sum, Complex.ofReal_mul]
  rw [fderiv_fun_sum (fun a _ => by fun_prop)]
  simp only [ContinuousLinearMap.sum_apply]
  have hd (a : Fin d) :
      fderiv ℝ (fun y : Vec d => (B j a : ℂ) * (y a : ℂ)) x (unitVector k) =
        (B j a : ℂ) * (unitVector k a : ℂ) := by
    rw [fderiv_const_mul (by fun_prop)]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, fderiv_complex_coordinate]
  simp_rw [hd]
  simp [unitVector, Pi.single_apply, apply_ite Complex.ofReal, mul_ite]

/-- Mixed second real spatial Fréchet derivatives, for arbitrary complex force. -/
theorem fderiv_fderiv_homogenizedGaussianKernel_complexForce_coordinate {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i j k : Fin d) (s : ℝ) (hs : 0 < s)
    (ζ : ℂ) (x : Vec d) :
    fderiv ℝ (fun y => fderiv ℝ (homogenizedGaussianKernel Q i s hs ζ) y (unitVector j))
        x (unitVector k) =
      ((ζ * (unitVector i j : ℂ) -
          (((homogenizedCoefficient Q)⁻¹).mulVec x j : ℂ) / (s : ℂ)) *
        (ζ * (unitVector i k : ℂ) -
          (((homogenizedCoefficient Q)⁻¹).mulVec x k : ℂ) / (s : ℂ)) -
        (((homogenizedCoefficient Q)⁻¹) j k : ℂ) / (s : ℂ)) *
          homogenizedGaussianKernel Q i s hs ζ x := by
  simp_rw [fderiv_homogenizedGaussianKernel_complexForce_coordinate]
  have hm : DifferentiableAt ℝ (fun y : Vec d =>
      (((homogenizedCoefficient Q)⁻¹).mulVec y j : ℂ)) x := by
    unfold Matrix.mulVec dotProduct
    fun_prop
  have hK := ((contDiff_homogenizedGaussianKernel_complexForce Q i s hs ζ).differentiable
    (by simp)).differentiableAt (x := x)
  rw [fderiv_fun_mul (by fun_prop) hK]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [fderiv_homogenizedGaussianKernel_complexForce_coordinate]
  simp_rw [div_eq_mul_inv]
  rw [fderiv_const_sub, fderiv_mul_const hm]
  simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [fderiv_complex_mulVec_coordinate]
  ring


private lemma clm_apply_coordinates (L : Vec d →L[ℝ] ℂ) (v : Vec d) :
    L v = ∑ j, (v j : ℂ) * L (unitVector j) := by
  have hv : v = ∑ j, v j • unitVector j := by
    ext k
    simp [unitVector, Pi.single_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_ite]
  conv_lhs => rw [hv, map_sum]
  simp only [map_smul, Complex.real_smul]

/-- The full first real spatial Fréchet derivative, evaluated on any direction. -/
theorem fderiv_homogenizedGaussianKernel_complexForce_apply {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (s : ℝ) (hs : 0 < s)
    (ζ : ℂ) (x v : Vec d) :
    fderiv ℝ (homogenizedGaussianKernel Q i s hs ζ) x v =
      (∑ j, (v j : ℂ) * (ζ * (unitVector i j : ℂ) -
        (((homogenizedCoefficient Q)⁻¹).mulVec x j : ℂ) / (s : ℂ))) *
          homogenizedGaussianKernel Q i s hs ζ x := by
  rw [clm_apply_coordinates]
  simp_rw [fderiv_homogenizedGaussianKernel_complexForce_coordinate]
  simp only [Finset.sum_mul, mul_assoc]

/-- The full mixed second real spatial Fréchet derivative on any two directions. -/
theorem fderiv_fderiv_homogenizedGaussianKernel_complexForce_apply {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (s : ℝ) (hs : 0 < s)
    (ζ : ℂ) (x v w : Vec d) :
    fderiv ℝ (fun y => fderiv ℝ (homogenizedGaussianKernel Q i s hs ζ) y v) x w =
      (∑ j, ∑ k, (v j : ℂ) * (w k : ℂ) *
        ((ζ * (unitVector i j : ℂ) -
            (((homogenizedCoefficient Q)⁻¹).mulVec x j : ℂ) / (s : ℂ)) *
          (ζ * (unitVector i k : ℂ) -
            (((homogenizedCoefficient Q)⁻¹).mulVec x k : ℂ) / (s : ℂ)) -
          (((homogenizedCoefficient Q)⁻¹) j k : ℂ) / (s : ℂ))) *
            homogenizedGaussianKernel Q i s hs ζ x := by
  have hK := ((contDiff_homogenizedGaussianKernel_complexForce Q i s hs ζ).differentiable
    (by simp)).differentiableAt (x := x)
  have hf (j : Fin d) : DifferentiableAt ℝ
      (fun y => fderiv ℝ (homogenizedGaussianKernel Q i s hs ζ) y (unitVector j)) x := by
    simp_rw [fderiv_homogenizedGaussianKernel_complexForce_coordinate]
    have hm : DifferentiableAt ℝ (fun y : Vec d =>
        (((homogenizedCoefficient Q)⁻¹).mulVec y j : ℂ)) x := by
      unfold Matrix.mulVec dotProduct
      fun_prop
    have ha : DifferentiableAt ℝ (fun y : Vec d => ζ * (unitVector i j : ℂ) -
        (((homogenizedCoefficient Q)⁻¹).mulVec y j : ℂ) / (s : ℂ)) x := by fun_prop
    exact ha.mul hK
  have heq : (fun y => fderiv ℝ (homogenizedGaussianKernel Q i s hs ζ) y v) =
      fun y => ∑ j, (v j : ℂ) *
        fderiv ℝ (homogenizedGaussianKernel Q i s hs ζ) y (unitVector j) := by
    funext y
    exact clm_apply_coordinates _ v
  rw [heq, fderiv_fun_sum (fun j _ => (hf j).const_mul _)]
  simp only [ContinuousLinearMap.sum_apply]
  simp_rw [fderiv_const_mul (hf _), ContinuousLinearMap.smul_apply, smul_eq_mul]
  simp_rw [clm_apply_coordinates (v := w),
    fderiv_fderiv_homogenizedGaussianKernel_complexForce_coordinate]
  simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]

/-- Time-one kernel value at real zero: the literal complex Gaussian shift. -/
theorem homogenizedGaussianKernel_complexForce_at_zero {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) :
    homogenizedGaussianKernel Q i 1 (by norm_num) ζ 0 =
      ((((2 * Real.pi) ^ (-(d : ℝ) / 2) /
        Real.sqrt (homogenizedCoefficient Q).det) : ℝ) : ℂ) *
          Complex.exp (-((homogenizedCoefficient Q i i / 2 : ℝ) : ℂ) * ζ ^ 2) := by
  have hq : (∑ j, ∑ k,
      ((0 : ℂ) - ζ * (1 : ℂ) * ((homogenizedCoefficient Q).mulVec (unitVector i) j : ℂ)) *
        (((homogenizedCoefficient Q)⁻¹) j k : ℂ) *
      ((0 : ℂ) - ζ * (1 : ℂ) * ((homogenizedCoefficient Q).mulVec (unitVector i) k : ℂ))) =
        ζ ^ 2 * (homogenizedCoefficient Q i i : ℂ) := by
    have hsum (j : Fin d) := inverse_shift_sum Q i j 1 ζ (0 : Vec d)
    simp only [Pi.zero_apply, Complex.ofReal_zero, Complex.ofReal_one,
      Matrix.mulVec_zero, zero_sub, mul_one] at hsum ⊢
    simp_rw [mul_assoc, ← Finset.mul_sum]
    simp_rw [hsum]
    simp [unitVector, Pi.single_apply, apply_ite Complex.ofReal, mul_ite,
      Matrix.mulVec, dotProduct]
    ring
  unfold homogenizedGaussianKernel
  simp only [Pi.zero_apply, Complex.ofReal_zero, Complex.ofReal_one, mul_one]
  rw [show (∑ j, ∑ k,
      ((0 : ℂ) - ζ * ((homogenizedCoefficient Q).mulVec (unitVector i) j : ℂ)) *
        (((homogenizedCoefficient Q)⁻¹) j k : ℂ) *
      ((0 : ℂ) - ζ * ((homogenizedCoefficient Q).mulVec (unitVector i) k : ℂ))) =
        ζ ^ 2 * (homogenizedCoefficient Q i i : ℂ) by simpa only [mul_one] using hq]
  congr 2
  simp only [Complex.ofReal_div, Complex.ofReal_ofNat]
  ring

/-- First derivative at zero, with the exact signed complex force factor. -/
theorem fderiv_homogenizedGaussianKernel_complexForce_at_zero {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i j : Fin d) (ζ : ℂ) :
    fderiv ℝ (homogenizedGaussianKernel Q i 1 (by norm_num) ζ) 0 (unitVector j) =
      ζ * (unitVector i j : ℂ) * homogenizedGaussianKernel Q i 1 (by norm_num) ζ 0 := by
  rw [fderiv_homogenizedGaussianKernel_complexForce_coordinate]
  simp only [Matrix.mulVec_zero, Pi.zero_apply, Complex.ofReal_zero, zero_div, sub_zero]

/-- Negative mixed Hessian at zero, including the full anisotropic inverse. -/
theorem neg_fderiv_fderiv_homogenizedGaussianKernel_complexForce_at_zero {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i j k : Fin d) (ζ : ℂ) :
    -fderiv ℝ (fun y => fderiv ℝ (homogenizedGaussianKernel Q i 1 (by norm_num) ζ)
        y (unitVector j)) 0 (unitVector k) =
      ((((homogenizedCoefficient Q)⁻¹) j k : ℂ) -
        ζ ^ 2 * (unitVector i j : ℂ) * (unitVector i k : ℂ)) *
          homogenizedGaussianKernel Q i 1 (by norm_num) ζ 0 := by
  rw [fderiv_fderiv_homogenizedGaussianKernel_complexForce_coordinate]
  simp only [Matrix.mulVec_zero, Pi.zero_apply, Complex.ofReal_zero, sub_zero,
    Complex.ofReal_one, div_one]
  ring


/-- The first derivative at zero in an arbitrary real spatial direction. -/
theorem fderiv_homogenizedGaussianKernel_complexForce_at_zero_apply {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (v : Vec d) :
    fderiv ℝ (homogenizedGaussianKernel Q i 1 (by norm_num) ζ) 0 v =
      ζ * (v i : ℂ) * homogenizedGaussianKernel Q i 1 (by norm_num) ζ 0 := by
  rw [clm_apply_coordinates]
  simp_rw [fderiv_homogenizedGaussianKernel_complexForce_at_zero]
  simp [unitVector, Pi.single_apply, apply_ite Complex.ofReal, mul_ite, ite_mul]
  ring

/-- The complete negative mixed Hessian at zero on two real spatial directions. -/
theorem neg_fderiv_fderiv_homogenizedGaussianKernel_complexForce_at_zero_apply {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (v w : Vec d) :
    -fderiv ℝ (fun y => fderiv ℝ (homogenizedGaussianKernel Q i 1 (by norm_num) ζ) y v) 0 w =
      ((∑ j, ∑ k, (v j : ℂ) * (w k : ℂ) * (((homogenizedCoefficient Q)⁻¹) j k : ℂ)) -
        ζ ^ 2 * (v i : ℂ) * (w i : ℂ)) * homogenizedGaussianKernel Q i 1 (by norm_num) ζ 0 := by
  rw [fderiv_fderiv_homogenizedGaussianKernel_complexForce_apply]
  simp only [Matrix.mulVec_zero, Pi.zero_apply, Complex.ofReal_zero, sub_zero,
    Complex.ofReal_one, div_one]
  have hd : (∑ j, ∑ k, (v j : ℂ) * (w k : ℂ) *
      ((ζ * (unitVector i j : ℂ)) * (ζ * (unitVector i k : ℂ)))) =
        ζ ^ 2 * (v i : ℂ) * (w i : ℂ) := by
    simp [unitVector, Pi.single_apply, apply_ite Complex.ofReal, mul_ite, ite_mul]
    ring
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [hd]
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


/-- Deterministic divergence and force contractions on the actual complex kernel
are exactly the frozen velocity profile, for every complex force. -/
theorem velocityGaussianProfile_eq_complexKernel_contraction {Λ₀ r₀ : ℝ} (hd : 2 ≤ d)
    (Q : EnvironmentLaw d Λ₀ r₀)
    (covariance : Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ)
    (i : Fin d) (ζ : ℂ) :
    let first : Fin d := ⟨0, by omega⟩
    let p := homogenizedGaussianKernel Q first 1 (by norm_num) ζ
    (1 / 4 : ℂ) * (∑ j, ∑ k,
      (-fderiv ℝ (fun y => fderiv ℝ p y (unitVector j)) 0 (unitVector k)) *
        (covariance (.inl (j, first)) (.inl (k, i)) : ℂ)) +
      ζ / 2 * (∑ j, fderiv ℝ p 0 (unitVector j) *
        (covariance (.inl (j, first)) (.inl (first, i)) : ℂ)) =
      velocityGaussianProfile hd Q covariance i ζ := by
  dsimp only
  simp_rw [neg_fderiv_fderiv_homogenizedGaussianKernel_complexForce_at_zero,
    fderiv_homogenizedGaussianKernel_complexForce_at_zero]
  erw [gaussian_velocity_contraction_algebra
    (fun j k => ((homogenizedCoefficient Q)⁻¹ j k : ℂ))
    (fun j k => (covariance (.inl (j, ⟨0, by omega⟩)) (.inl (k, i)) : ℂ))
    (⟨0, by omega⟩ : Fin d) ζ,
    homogenizedGaussianKernel_complexForce_at_zero]
  unfold velocityGaussianProfile
  simp only [Complex.ofReal_sum, Complex.ofReal_mul]
  ring

/-- The actual complex-force clock contraction is the frozen clock profile. -/
theorem clockGaussianProfile_eq_complexKernel_contraction {Λ₀ r₀ : ℝ} (hd : 2 ≤ d)
    (Q : EnvironmentLaw d Λ₀ r₀)
    (covariance : Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ) (ζ : ℂ) :
    let first : Fin d := ⟨0, by omega⟩
    let p := homogenizedGaussianKernel Q first 1 (by norm_num) ζ
    ζ / 2 * (∑ j, fderiv ℝ p 0 (unitVector j) *
      (covariance (.inl (j, first)) (.inr ()) : ℂ)) =
        clockGaussianProfile hd Q covariance ζ := by
  dsimp only
  simp_rw [fderiv_homogenizedGaussianKernel_complexForce_at_zero]
  simp only [unitVector, Pi.single_apply, apply_ite Complex.ofReal, Complex.ofReal_one,
    Complex.ofReal_zero, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hp := homogenizedGaussianKernel_complexForce_at_zero Q ⟨0, by omega⟩ ζ
  rw [hp]
  unfold clockGaussianProfile
  ring

end EinsteinFull
