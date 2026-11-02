import EinsteinFull.Work.W4.HomogeneousGaussianTimeDerivativeSupport

/-!
Scale-explicit bounds for the literal homogeneous Gaussian time derivative.
The inverse quadratic polynomial is absorbed into the same anisotropic density
at time `4t`; no isotropic replacement or extra moment premise is used.
-/

open MeasureTheory Filter
open scoped Topology BigOperators
noncomputable section
namespace EinsteinFull
open EinsteinRelation

variable {d : ℕ} {Λ r : ℝ}

private lemma derivativeBound_reduced_pos (Λ : ℝ) : 0 < sourceReducedBound Λ := by
  unfold sourceReducedBound
  exact mul_pos (Real.exp_pos _) (by nlinarith [sq_nonneg Λ])

private lemma derivativeBound_norm_sq (x : Vec d) : euclideanNorm x ^ 2 = euclideanSq x := by
  apply Real.sq_sqrt
  unfold euclideanSq dot
  exact Finset.sum_nonneg fun j _ => mul_self_nonneg (x j)

private lemma derivativeBound_coord (x : Vec d) (i : Fin d) :
    |x i| ≤ euclideanNorm x := by
  apply le_of_sq_le_sq _ (Real.sqrt_nonneg _)
  change |x i| ^ 2 ≤ euclideanNorm x ^ 2
  rw [sq_abs, derivativeBound_norm_sq]
  simpa only [euclideanSq, dot, pow_two] using Finset.single_le_sum (fun j _ => mul_self_nonneg (x j)) (Finset.mem_univ i)

private lemma derivativeBound_entry (Q : EnvironmentLaw d Λ r) (i : Fin d) :
    |homogenizedCoefficient Q i i| ≤ sourceReducedBound Λ := by
  have h := (derivativeBound_coord ((homogenizedCoefficient Q).mulVec (unitVector i)) i).trans
    (homogenizedMatrix_euclideanNorm_mulVec_unitVector_le Q i)
  simpa [Matrix.mulVec, dotProduct, unitVector, Pi.single_apply, mul_ite] using h

private lemma derivativeBound_quadratic (Q : EnvironmentLaw d Λ r) (x : Vec d) :
    (∑ j, ∑ k, x j * ((homogenizedCoefficient Q)⁻¹) j k * x k) =
      dot x ((homogenizedCoefficient Q)⁻¹.mulVec x) := by
  simp only [dot, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

/-- Exact determinant-preserving dilation identity for a quadratic exponential. -/
theorem anisotropicGaussian_four_time (A : Mat d) (t : ℝ) (ht : 0 < t) (x : Vec d) :
    (2 * Real.pi * t) ^ (-(d : ℝ) / 2) / Real.sqrt A.det *
      Real.exp (-(∑ j, ∑ k, x j * (A⁻¹) j k * x k) / (8 * t)) =
        (4 : ℝ) ^ ((d : ℝ) / 2) * anisotropicGaussian A (4 * t) x := by
  have hp : (2 * Real.pi * (4 * t)) ^ (-(d : ℝ) / 2) =
      (4 : ℝ) ^ (-(d : ℝ) / 2) * (2 * Real.pi * t) ^ (-(d : ℝ) / 2) := by
    rw [show 2 * Real.pi * (4 * t) = 4 * (2 * Real.pi * t) by ring,
      Real.mul_rpow (by norm_num) (by positivity)]
  have hc : (4 : ℝ) ^ ((d : ℝ) / 2) * (4 : ℝ) ^ (-(d : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add (by norm_num),
      show (d : ℝ) / 2 + -(d : ℝ) / 2 = 0 by ring, Real.rpow_zero]
  unfold anisotropicGaussian
  rw [hp, show 2 * (4 * t) = 8 * t by ring]
  calc
    _ = ((4 : ℝ) ^ ((d : ℝ) / 2) * (4 : ℝ) ^ (-(d : ℝ) / 2)) *
        ((2 * Real.pi * t) ^ (-(d : ℝ) / 2) / Real.sqrt A.det *
          Real.exp (-(∑ j, ∑ k, x j * (A⁻¹) j k * x k) / (8 * t))) := by rw [hc, one_mul]
    _ = _ := by ring

/-- The actual inverse quadratic polynomial has a Gaussian envelope at scale t.
This elementary estimate supplies the moment bound, rather than assuming it. -/
theorem quadratic_time_derivative_absorption (a q t : ℝ) (ha : 0 ≤ a)
    (hq : 0 ≤ q) (ht : 0 < t) :
    (a + q / (2 * t ^ 2)) * Real.exp (-q / (4 * t)) ≤
      (a + 4 / t) * Real.exp (-q / (8 * t)) := by
  have h1 : Real.exp (-q / (8 * t)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr hq) (by positivity))
  have h2 : q / (8 * t) * Real.exp (-q / (8 * t)) ≤ 1 := by
    have hh : q / (8 * t) ≤ Real.exp (q / (8 * t)) :=
      (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
    calc
      _ ≤ Real.exp (q / (8 * t)) * Real.exp (-q / (8 * t)) :=
        mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le
      _ = 1 := by
        rw [← Real.exp_add, show q / (8 * t) + -q / (8 * t) = 0 by ring, Real.exp_zero]
  have hp : (a + q / (2 * t ^ 2)) * Real.exp (-q / (8 * t)) ≤ a + 4 / t := by
    have heq : q / (2 * t ^ 2) = (4 / t) * (q / (8 * t)) := by field_simp; ring
    rw [add_mul, heq, mul_assoc]
    exact add_le_add (by simpa using mul_le_mul_of_nonneg_left h1 ha)
      (by simpa using mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 4 / t))
  calc
    _ = ((a + q / (2 * t ^ 2)) * Real.exp (-q / (8 * t))) *
        Real.exp (-q / (8 * t)) := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le

private lemma derivativeBound_tilt (Q : EnvironmentLaw d Λ r) (i : Fin d)
    (t : ℝ) (ht : 0 < t) (ζ : ℂ) (x : Vec d) :
    (ζ * (x i : ℂ) - ζ ^ 2 * (t : ℂ) * (homogenizedCoefficient Q i i : ℂ) / 2).re ≤
      2 * sourceReducedBound Λ * t * ‖ζ‖ ^ 2 +
        (∑ j, ∑ k, x j * ((homogenizedCoefficient Q)⁻¹) j k * x k) / (4 * t) := by
  let K := sourceReducedBound Λ
  have hK : 0 < K := derivativeBound_reduced_pos Λ
  have hq := (homogenizedCoefficient_inv_quadratic_bounds Q x).1
  rw [← derivativeBound_norm_sq, ← derivativeBound_quadratic] at hq
  have hy : ‖ζ‖ * euclideanNorm x ≤ euclideanNorm x ^ 2 / (4 * K * t) + K * t * ‖ζ‖ ^ 2 := by
    apply (mul_le_mul_iff_right₀ (by positivity : 0 < 4 * K * t)).mp
    field_simp
    nlinarith only [sq_nonneg (euclideanNorm x - 2 * K * t * ‖ζ‖)]
  have hdiv : euclideanNorm x ^ 2 / (4 * K * t) ≤
      (∑ j, ∑ k, x j * ((homogenizedCoefficient Q)⁻¹) j k * x k) / (4 * t) := by
    calc
      _ = (K⁻¹ * euclideanNorm x ^ 2) / (4 * t) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hq (by positivity)
  calc
    _ ≤ ‖ζ * (x i : ℂ) - ζ ^ 2 * (t : ℂ) * (homogenizedCoefficient Q i i : ℂ) / 2‖ :=
      Complex.re_le_norm _
    _ ≤ ‖ζ * (x i : ℂ)‖ + ‖ζ ^ 2 * (t : ℂ) * (homogenizedCoefficient Q i i : ℂ) / 2‖ :=
      norm_sub_le _ _
    _ = ‖ζ‖ * |x i| + ‖ζ‖ ^ 2 * t * |homogenizedCoefficient Q i i| / 2 := by
      simp only [norm_mul, norm_pow, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
      norm_num
    _ ≤ ‖ζ‖ * euclideanNorm x + ‖ζ‖ ^ 2 * t * K / 2 := by
      gcongr
      · exact derivativeBound_coord x i
      · exact derivativeBound_entry Q i
    _ ≤ _ := by nlinarith only [hy, hdiv, mul_nonneg (mul_nonneg hK.le ht.le) (sq_nonneg ‖ζ‖)]

/-- Pointwise anisotropic envelope with the correct inverse-time scale. -/
theorem norm_homogenizedGaussianKernelTimeDerivative_le_four_time
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (t : ℝ) (ht : 0 < t) (ζ : ℂ) (x : Vec d) :
    ‖homogenizedGaussianKernelTimeDerivative Q i t ht ζ x‖ ≤
      ((d : ℝ) / (2 * t) + 4 / t + ‖ζ‖ ^ 2 * sourceReducedBound Λ / 2) *
        (4 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (2 * sourceReducedBound Λ * t * ‖ζ‖ ^ 2) *
          anisotropicGaussian (homogenizedCoefficient Q) (4 * t) x := by
  let q := ∑ j, ∑ k, x j * ((homogenizedCoefficient Q)⁻¹) j k * x k
  let p := (2 * Real.pi * t) ^ (-(d : ℝ) / 2) / Real.sqrt (homogenizedCoefficient Q).det
  let a := (d : ℝ) / (2 * t) + ‖ζ‖ ^ 2 * sourceReducedBound Λ / 2
  have hK := derivativeBound_reduced_pos Λ
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hq : 0 ≤ q := by
    dsimp only [q]
    rw [derivativeBound_quadratic]
    exact (mul_nonneg (inv_nonneg.mpr hK.le) (by
      rw [← derivativeBound_norm_sq]; positivity)).trans
        (homogenizedCoefficient_inv_quadratic_bounds Q x).1
  have hf : ‖((-(d : ℝ) / (2 * t) + q / (2 * t ^ 2) : ℝ) : ℂ) -
      ζ ^ 2 * (homogenizedCoefficient Q i i : ℂ) / 2‖ ≤ a + q / (2 * t ^ 2) := by
    calc
      _ ≤ ‖((-(d : ℝ) / (2 * t) + q / (2 * t ^ 2) : ℝ) : ℂ)‖ +
          ‖ζ ^ 2 * (homogenizedCoefficient Q i i : ℂ) / 2‖ := norm_sub_le _ _
      _ ≤ (d : ℝ) / (2 * t) + q / (2 * t ^ 2) + ‖ζ‖ ^ 2 * |homogenizedCoefficient Q i i| / 2 := by
        simp only [Complex.norm_real, Real.norm_eq_abs, norm_div, norm_mul, norm_pow]
        norm_num only [Complex.norm_ofNat]
        apply add_le_add _ le_rfl
        exact (abs_add_le _ _).trans (by
          rw [abs_div, abs_neg, abs_of_nonneg (Nat.cast_nonneg d),
            abs_of_pos (by positivity : 0 < 2 * t), abs_of_nonneg (by positivity : 0 ≤ q / (2 * t ^ 2))])
      _ ≤ _ := by
        dsimp [a]
        have h := mul_le_mul_of_nonneg_left (derivativeBound_entry Q i) (sq_nonneg ‖ζ‖)
        linarith only [h]
  have hk : ‖homogenizedGaussianKernel Q i t ht ζ x‖ ≤
      p * Real.exp (2 * sourceReducedBound Λ * t * ‖ζ‖ ^ 2) * Real.exp (-q / (4 * t)) := by
    rw [homogenizedGaussianKernel_eq_exp_tilt, norm_mul, Complex.norm_exp,
      Complex.norm_real, Real.norm_eq_abs]
    change Real.exp _ * |p * Real.exp (-q / (2 * t))| ≤ _
    rw [abs_of_nonneg (by positivity : 0 ≤ p * Real.exp (-q / (2 * t)))]
    calc
      _ = p * Real.exp ((ζ * (x i : ℂ) - ζ ^ 2 * (t : ℂ) *
          (homogenizedCoefficient Q i i : ℂ) / 2).re - q / (2 * t)) := by
        rw [Real.exp_sub, neg_div, Real.exp_neg]; ring
      _ ≤ p * Real.exp (2 * sourceReducedBound Λ * t * ‖ζ‖ ^ 2 - q / (4 * t)) := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) hp
        have h := derivativeBound_tilt Q i t ht ζ x
        change _ ≤ 2 * sourceReducedBound Λ * t * ‖ζ‖ ^ 2 + q / (4 * t) at h
        rw [show q / (2 * t) = 2 * (q / (4 * t)) by ring]
        linarith only [h]
      _ = _ := by rw [Real.exp_sub, neg_div, Real.exp_neg]; ring
  calc
    _ ≤ (a + q / (2 * t ^ 2)) *
        (p * Real.exp (2 * sourceReducedBound Λ * t * ‖ζ‖ ^ 2) * Real.exp (-q / (4 * t))) := by
      unfold homogenizedGaussianKernelTimeDerivative
      rw [norm_mul]
      exact mul_le_mul hf hk (norm_nonneg _) (by positivity)
    _ = (p * Real.exp (2 * sourceReducedBound Λ * t * ‖ζ‖ ^ 2)) *
        ((a + q / (2 * t ^ 2)) * Real.exp (-q / (4 * t))) := by ring
    _ ≤ (p * Real.exp (2 * sourceReducedBound Λ * t * ‖ζ‖ ^ 2)) *
        ((a + 4 / t) * Real.exp (-q / (8 * t))) :=
      mul_le_mul_of_nonneg_left (quadratic_time_derivative_absorption a q t ha hq ht) (by positivity)
    _ = (a + 4 / t) * Real.exp (2 * sourceReducedBound Λ * t * ‖ζ‖ ^ 2) *
        (p * Real.exp (-q / (8 * t))) := by ring
    _ = _ := by
      dsimp only [p, q]
      rw [anisotropicGaussian_four_time _ t ht x]
      dsimp only [a]
      ring

/-- Integrating the polynomial envelope retains exact Gaussian mass one. -/
theorem integral_norm_homogenizedGaussianKernelTimeDerivative_le_explicit
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (t : ℝ) (ht : 0 < t) (ζ : ℂ) :
    (∫ x : Vec d, ‖homogenizedGaussianKernelTimeDerivative Q i t ht ζ x‖) ≤
      ((d : ℝ) / (2 * t) + 4 / t + ‖ζ‖ ^ 2 * sourceReducedBound Λ / 2) *
        (4 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (2 * sourceReducedBound Λ * t * ‖ζ‖ ^ 2) := by
  let B := ((d : ℝ) / (2 * t) + 4 / t + ‖ζ‖ ^ 2 * sourceReducedBound Λ / 2) *
    (4 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (2 * sourceReducedBound Λ * t * ‖ζ‖ ^ 2)
  calc
    _ ≤ ∫ x : Vec d, B * anisotropicGaussian (homogenizedCoefficient Q) (4 * t) x :=
      integral_mono (integrable_homogenizedGaussianKernelTimeDerivative Q i t ht ζ).norm
        ((integrable_anisotropicGaussian _ (posDef_homogenizedCoefficient Q)
          (4 * t) (by positivity)).const_mul B)
        (norm_homogenizedGaussianKernelTimeDerivative_le_four_time Q i t ht ζ)
    _ = _ := by
      rw [integral_const_mul, integral_anisotropicGaussian _
        (posDef_homogenizedCoefficient Q) (4 * t) (by positivity), mul_one]

/-- A structural constant chosen before law, coordinate, complex force and time. -/
def homogeneousGaussianTimeDerivativeBound (d : ℕ) (Λ : ℝ) : ℝ :=
  ((d : ℝ) / 2 + 4 + sourceReducedBound Λ / 2) * (4 : ℝ) ^ ((d : ℝ) / 2) +
    2 * sourceReducedBound Λ + 1

/-- Positivity of the structural constant needs no realization or force. -/
theorem homogeneousGaussianTimeDerivativeBound_pos (d : ℕ) (Λ : ℝ) :
    0 < homogeneousGaussianTimeDerivativeBound d Λ := by
  have hK := derivativeBound_reduced_pos Λ
  unfold homogeneousGaussianTimeDerivativeBound
  positivity

/-- Scale-explicit structural L1 estimate for the literal derivative kernel. -/
theorem integral_norm_homogenizedGaussianKernelTimeDerivative_le
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (t : ℝ) (ht : 0 < t) (ζ : ℂ) :
    (∫ x : Vec d, ‖homogenizedGaussianKernelTimeDerivative Q i t ht ζ x‖) ≤
      homogeneousGaussianTimeDerivativeBound d Λ * (t⁻¹ + ‖ζ‖ ^ 2) *
        Real.exp (homogeneousGaussianTimeDerivativeBound d Λ * ‖ζ‖ ^ 2 * t) := by
  let K := sourceReducedBound Λ
  let B := (d : ℝ) / 2 + 4 + K / 2
  let F := (4 : ℝ) ^ ((d : ℝ) / 2)
  let C := homogeneousGaussianTimeDerivativeBound d Λ
  have hK : 0 < K := derivativeBound_reduced_pos Λ
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hC : 0 < C := homogeneousGaussianTimeDerivativeBound_pos d Λ
  have hBC : B * F ≤ C := by
    dsimp [C, homogeneousGaussianTimeDerivativeBound, B, F, K]
    linarith only [hK]
  have hKC : 2 * K ≤ C := by
    change 2 * K ≤ B * F + 2 * K + 1
    linarith only [mul_nonneg hB hF]
  have hp : (d : ℝ) / (2 * t) + 4 / t + ‖ζ‖ ^ 2 * K / 2 ≤ B * (t⁻¹ + ‖ζ‖ ^ 2) := by
    have h0 : 0 ≤ (d : ℝ) / 2 + 4 := by positivity
    have h1 : 0 ≤ K / 2 := by positivity
    have h2 : 0 ≤ t⁻¹ := inv_nonneg.mpr ht.le
    dsimp [B]
    rw [show (d : ℝ) / (2 * t) = ((d : ℝ) / 2) * t⁻¹ by ring,
      show 4 / t = 4 * t⁻¹ by ring]
    nlinarith only [mul_nonneg h0 (sq_nonneg ‖ζ‖), mul_nonneg h1 h2]
  apply (integral_norm_homogenizedGaussianKernelTimeDerivative_le_explicit Q i t ht ζ).trans
  calc
    _ ≤ (B * (t⁻¹ + ‖ζ‖ ^ 2)) * F * Real.exp (2 * K * t * ‖ζ‖ ^ 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp hF) (Real.exp_pos _).le
    _ ≤ C * (t⁻¹ + ‖ζ‖ ^ 2) * Real.exp (C * ‖ζ‖ ^ 2 * t) := by
      apply mul_le_mul
      · rw [mul_right_comm B _ F]
        exact mul_le_mul_of_nonneg_right hBC (by positivity)
      · apply Real.exp_le_exp.mpr
        nlinarith only [mul_le_mul_of_nonneg_right hKC
          (mul_nonneg (sq_nonneg ‖ζ‖) ht.le)]
      · positivity
      · positivity

/-- Applying the stationary translation isometry to the actual derivative. -/
theorem norm_homogeneousAverageTimeDerivative_le
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (t : ℝ) (ht : 0 < t)
    (ζ : ℂ) (f : Lp ℂ 2 (reducedLaw Q)) :
    ‖∫ x : Vec d, homogenizedGaussianKernelTimeDerivative Q i t ht ζ x •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f‖ ≤
      homogeneousGaussianTimeDerivativeBound d Λ * (t⁻¹ + ‖ζ‖ ^ 2) *
        Real.exp (homogeneousGaussianTimeDerivativeBound d Λ * ‖ζ‖ ^ 2 * t) * ‖f‖ := by
  calc
    _ ≤ ∫ x : Vec d, ‖homogenizedGaussianKernelTimeDerivative Q i t ht ζ x •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f‖ :=
      norm_integral_le_integral_norm _
    _ = (∫ x : Vec d, ‖homogenizedGaussianKernelTimeDerivative Q i t ht ζ x‖) * ‖f‖ := by
      simp_rw [norm_smul, norm_complexTranslation]
      rw [integral_mul_const]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (integral_norm_homogenizedGaussianKernelTimeDerivative_le Q i t ht ζ) (norm_nonneg _)

/-- Bound on the strong positive-time derivative for every stationary L2 datum. -/
theorem norm_deriv_homogeneousGaussianEvolution_time_le
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (ζ : ℂ)
    (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ) (ht : 0 < t) :
    ‖deriv (fun s : ℝ => homogeneousGaussianEvolution Q i ζ
      ⟨max s 0, le_max_right _ _⟩ f) t‖ ≤
      homogeneousGaussianTimeDerivativeBound d Λ * (t⁻¹ + ‖ζ‖ ^ 2) *
        Real.exp (homogeneousGaussianTimeDerivativeBound d Λ * ‖ζ‖ ^ 2 * t) * ‖f‖ := by
  rw [(hasDerivAt_homogeneousGaussianEvolution_time Q i ζ f t ht).deriv]
  exact norm_homogeneousAverageTimeDerivative_le Q i t ht ζ f

/-- Explicit witness order: one constant for every law, coordinate, force,
positive time and L2 datum, with both the literal kernel and orbit bounds. -/
theorem exists_homogeneousGaussianTimeDerivative_scale_bound (d : ℕ) (Λ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℝ) (Q : EnvironmentLaw d Λ r) (i : Fin d)
      (ζ : ℂ) (t : ℝ) (ht : 0 < t),
      (∫ x : Vec d, ‖homogenizedGaussianKernelTimeDerivative Q i t ht ζ x‖) ≤
        C * (t⁻¹ + ‖ζ‖ ^ 2) * Real.exp (C * ‖ζ‖ ^ 2 * t) ∧
      ∀ f : Lp ℂ 2 (reducedLaw Q),
        ‖deriv (fun s : ℝ => homogeneousGaussianEvolution Q i ζ
          ⟨max s 0, le_max_right _ _⟩ f) t‖ ≤
            C * (t⁻¹ + ‖ζ‖ ^ 2) * Real.exp (C * ‖ζ‖ ^ 2 * t) * ‖f‖ := by
  refine ⟨homogeneousGaussianTimeDerivativeBound d Λ,
    homogeneousGaussianTimeDerivativeBound_pos d Λ, ?_⟩
  intro r Q i ζ t ht
  exact ⟨integral_norm_homogenizedGaussianKernelTimeDerivative_le Q i t ht ζ,
    fun f => norm_deriv_homogeneousGaussianEvolution_time_le Q i ζ f t ht⟩

end EinsteinFull
