import EinsteinFull.Work.W3.GaussianConvolutionSupport
import EinsteinRelation.Correctors.EllipticInverseBounds
import EinsteinRelation.Correctors.EllipticOperatorBound
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# Uniform weighted bounds for the actual complex Gaussian model kernels

Deterministic bounds used before the covariance replacement in
`paper/main.tex:1245–1251`. The coefficient is the actual variational
`homogenizedCoefficient Q`, not a scalar comparison kernel. All spatial
weights and direction bounds use the explicit Euclidean norm on `Vec d`.
-/

namespace EinsteinFull

open EinsteinRelation
open scoped BigOperators

variable {d : ℕ}

private lemma reducedBound_pos {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) :
    0 < sourceReducedBound Λ₀ := by
  unfold sourceReducedBound
  exact mul_pos (Real.exp_pos _) (by nlinarith [Q.ellipticity_parameter, sq_nonneg Λ₀])

private lemma euclideanNorm_sq (x : Vec d) : euclideanNorm x ^ 2 = euclideanSq x := by
  apply Real.sq_sqrt
  unfold euclideanSq dot
  exact Finset.sum_nonneg (fun j _ => mul_self_nonneg (x j))

private lemma coord_le_euclideanNorm (x : Vec d) (j : Fin d) : |x j| ≤ euclideanNorm x := by
  have hn : 0 ≤ euclideanNorm x := Real.sqrt_nonneg _
  apply le_of_sq_le_sq _ hn
  rw [sq_abs, euclideanNorm_sq]
  simpa only [euclideanSq, dot, pow_two] using
    Finset.single_le_sum (fun k _ => mul_self_nonneg (x k)) (Finset.mem_univ j)

/-- Both inverse quadratic bounds are discharged from the actual environment law. -/
theorem homogenizedCoefficient_inv_quadratic_bounds {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (x : Vec d) :
    (sourceReducedBound Λ₀)⁻¹ * euclideanSq x ≤
        dot x ((homogenizedCoefficient Q)⁻¹.mulVec x) ∧
      dot x ((homogenizedCoefficient Q)⁻¹.mulVec x) ≤
        sourceReducedBound Λ₀ * euclideanSq x := by
  exact ((Correctors.isElliptic_inverse (reducedBound_pos Q)
    (homogenizedMatrix_isElliptic Q)) (0 : Vec d)).2 x

/-- The actual inverse has the same uniform Euclidean operator bound. -/
theorem homogenizedCoefficient_inv_mulVec_bound {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (x : Vec d) :
    euclideanNorm ((homogenizedCoefficient Q)⁻¹.mulVec x) ≤
      sourceReducedBound Λ₀ * euclideanNorm x := by
  exact Correctors.isElliptic_mulVec_euclideanNorm_le (reducedBound_pos Q)
    (Correctors.isElliptic_inverse (reducedBound_pos Q)
      (homogenizedMatrix_isElliptic Q)) (0 : Vec d) x

/-- Each inverse entry is bounded without a determinant or spectral premise. -/
theorem abs_homogenizedCoefficient_inv_entry_le {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (j k : Fin d) :
    |((homogenizedCoefficient Q)⁻¹) j k| ≤ sourceReducedBound Λ₀ := by
  have h := (coord_le_euclideanNorm ((homogenizedCoefficient Q)⁻¹.mulVec
    (unitVector k)) j).trans (homogenizedCoefficient_inv_mulVec_bound Q (unitVector k))
  simpa [unitVector, Matrix.mulVec, dotProduct, euclideanNorm, euclideanSq, dot,
    Pi.single_apply, mul_ite, ite_mul] using h

private lemma abs_det_le_entry_bound (B : Mat d) {K : ℝ}
    (hB : ∀ j k, |B j k| ≤ K) :
    |B.det| ≤ (Fintype.card (Equiv.Perm (Fin d)) : ℝ) * K ^ d := by
  rw [Matrix.det_apply']
  calc
    _ ≤ ∑ σ : Equiv.Perm (Fin d), |((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∏ j, B (σ j) j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ σ : Equiv.Perm (Fin d), ∏ j, |B (σ j) j| := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [abs_mul, Finset.abs_prod]
      have hsign : |((Equiv.Perm.sign σ : ℤ) : ℝ)| = 1 := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
      rw [hsign, one_mul]
    _ ≤ ∑ _σ : Equiv.Perm (Fin d), ∏ _j : Fin d, K := by
      apply Finset.sum_le_sum
      intro σ _
      exact Finset.prod_le_prod₀ (fun j _ => abs_nonneg _) (fun j _ => hB (σ j) j)
    _ = _ := by simp

/-- An explicit structural bound for the reciprocal determinant normalization. -/
theorem inv_sqrt_det_homogenizedCoefficient_le {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) :
    (Real.sqrt (homogenizedCoefficient Q).det)⁻¹ ≤
      Real.sqrt ((Fintype.card (Equiv.Perm (Fin d)) : ℝ) * (sourceReducedBound Λ₀) ^ d) := by
  rw [← Real.sqrt_inv]
  apply Real.sqrt_le_sqrt
  rw [← Ring.inverse_eq_inv, ← Matrix.det_nonsing_inv]
  exact (le_abs_self _).trans (abs_det_le_entry_bound _
    (abs_homogenizedCoefficient_inv_entry_le Q))

private lemma abs_homogenizedCoefficient_entry_le {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (j k : Fin d) :
    |homogenizedCoefficient Q j k| ≤ sourceReducedBound Λ₀ := by
  have h := (coord_le_euclideanNorm ((homogenizedCoefficient Q).mulVec
    (unitVector k)) j).trans (homogenizedMatrix_euclideanNorm_mulVec_unitVector_le Q k)
  simpa [unitVector, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite] using h

private lemma gaussian_tilt_re_le {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) (ζ : ℂ) (x : Vec d) :
    (ζ * (x i : ℂ) - ζ ^ 2 * (s : ℂ) * (homogenizedCoefficient Q i i : ℂ) / 2).re ≤
      ‖ζ‖ * euclideanNorm x + ‖ζ‖ ^ 2 * sourceReducedBound Λ₀ / 2 := by
  calc
    _ ≤ ‖ζ * (x i : ℂ) - ζ ^ 2 * (s : ℂ) *
        (homogenizedCoefficient Q i i : ℂ) / 2‖ := Complex.re_le_norm _
    _ ≤ ‖ζ * (x i : ℂ)‖ + ‖ζ ^ 2 * (s : ℂ) *
        (homogenizedCoefficient Q i i : ℂ) / 2‖ := norm_sub_le _ _
    _ = ‖ζ‖ * |x i| + ‖ζ‖ ^ 2 * s * |homogenizedCoefficient Q i i| / 2 := by
      simp only [norm_mul, norm_pow, norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hs]
      norm_num
    _ ≤ _ := by
      have ha := abs_homogenizedCoefficient_entry_le Q i i
      have hm : s * |homogenizedCoefficient Q i i| ≤ sourceReducedBound Λ₀ :=
        (mul_le_mul_of_nonneg_right hs1 (abs_nonneg _)).trans (by simpa using ha)
      nlinarith [mul_le_mul_of_nonneg_left (coord_le_euclideanNorm x i) (norm_nonneg ζ),
        mul_le_mul_of_nonneg_left hm (sq_nonneg ‖ζ‖)]

private lemma gaussian_exponent_le {K r u q s : ℝ} (hK : 0 < K) (hs : 0 < s)
    (hs1 : s ≤ 1) (hq : K⁻¹ * r ^ 2 ≤ q) :
    u * r + u ^ 2 * K / 2 - q / (2 * s) ≤ 2 * K * u ^ 2 - r ^ 2 / (4 * K) := by
  have hq0 : 0 ≤ q := (mul_nonneg (inv_nonneg.mpr hK.le) (sq_nonneg r)).trans hq
  have hd : r ^ 2 / (2 * K) ≤ q / (2 * s) := by
    calc
      _ = (K⁻¹ * r ^ 2) / 2 := by ring
      _ ≤ q / 2 := div_le_div_of_nonneg_right hq (by norm_num)
      _ ≤ _ := div_le_div_of_nonneg_left hq0 (by positivity) (by linarith)
  have hy : u * r ≤ r ^ 2 / (4 * K) + K * u ^ 2 := by
    apply (mul_le_mul_iff_right₀ (by positivity : 0 < 4 * K)).mp
    field_simp
    nlinarith only [sq_nonneg (r - 2 * K * u)]
  have hd' : 2 * (r ^ 2 / (4 * K)) ≤ q / (2 * s) := by
    convert hd using 1
    ring
  nlinarith only [hd', hy, mul_nonneg hK.le (sq_nonneg u)]

/-- Gaussian decay for every complex force, uniformly on times `[1/2,1]`.
The explicit coefficient depends only on dimension and the structural bound. -/
theorem norm_homogenizedGaussianKernel_le_gaussian {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (s : ℝ) (hs : 0 < s)
    (hslo : 1 / 2 ≤ s) (hshi : s ≤ 1) (ζ : ℂ) (x : Vec d) :
    ‖homogenizedGaussianKernel Q i s hs ζ x‖ ≤
      Real.sqrt ((Fintype.card (Equiv.Perm (Fin d)) : ℝ) * (sourceReducedBound Λ₀) ^ d) *
        Real.exp (2 * sourceReducedBound Λ₀ * ‖ζ‖ ^ 2 -
          euclideanNorm x ^ 2 / (4 * sourceReducedBound Λ₀)) := by
  let q := dot x ((homogenizedCoefficient Q)⁻¹.mulVec x)
  let pref := (2 * Real.pi * s) ^ (-(d : ℝ) / 2) / Real.sqrt (homogenizedCoefficient Q).det
  have hp0 : 0 ≤ pref := div_nonneg (Real.rpow_nonneg (by positivity) _) (Real.sqrt_nonneg _)
  have hp : pref ≤ Real.sqrt ((Fintype.card (Equiv.Perm (Fin d)) : ℝ) *
      (sourceReducedBound Λ₀) ^ d) := by
    have hb : 1 ≤ 2 * Real.pi * s := by
      nlinarith [mul_le_mul_of_nonneg_left hslo Real.pi_pos.le, Real.two_le_pi]
    have hr : (2 * Real.pi * s) ^ (-(d : ℝ) / 2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hb (by
        apply div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg d)) (by norm_num))
    exact (div_le_div_of_nonneg_right hr (Real.sqrt_nonneg _)).trans
      (by simpa only [one_div] using inv_sqrt_det_homogenizedCoefficient_le Q)
  have hq := (homogenizedCoefficient_inv_quadratic_bounds Q x).1
  rw [← euclideanNorm_sq x] at hq
  have he := (sub_le_sub_right (gaussian_tilt_re_le Q i s hs hshi ζ x) (q / (2 * s))).trans
    (gaussian_exponent_le (reducedBound_pos Q) hs hshi hq)
  rw [homogenizedGaussianKernel_eq_exp_tilt, norm_mul, Complex.norm_exp,
    Complex.norm_real, Real.norm_eq_abs]
  have heq : anisotropicGaussian (homogenizedCoefficient Q) s x =
      pref * Real.exp (-q / (2 * s)) := by
    change pref * Real.exp (-(∑ j, ∑ k, x j * ((homogenizedCoefficient Q)⁻¹) j k * x k) /
      (2 * s)) = _
    unfold q dot Matrix.mulVec dotProduct
    simp only [Finset.mul_sum, mul_assoc]
  rw [heq, abs_of_nonneg (mul_nonneg hp0 (Real.exp_pos _).le)]
  calc
    _ = pref * Real.exp ((ζ * (x i : ℂ) - ζ ^ 2 * (s : ℂ) *
        (homogenizedCoefficient Q i i : ℂ) / 2).re - q / (2 * s)) := by
      rw [Real.exp_sub, neg_div, Real.exp_neg]
      ring
    _ ≤ _ := mul_le_mul hp (Real.exp_le_exp.mpr he) (Real.exp_pos _).le
      (Real.sqrt_nonneg _)

private lemma gaussian_polynomial_absorption {K r u : ℝ} (hK : 0 < K)
    (hr : 0 ≤ r) (hu : 0 ≤ u) (n : ℕ) :
    (1 + r) ^ n * (1 + u) ^ 2 * Real.exp (2 * K * u ^ 2 - r ^ 2 / (4 * K)) ≤
      Real.exp (K * (n : ℝ) ^ 2) * Real.exp ((2 * K + 2) * (1 + u) ^ 2) := by
  have hp (t : ℝ) (ht : 0 ≤ t) (m : ℕ) : (1 + t) ^ m ≤ Real.exp ((m : ℝ) * t) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp t]) m
  have hy : (n : ℝ) * r - r ^ 2 / (4 * K) ≤ K * (n : ℝ) ^ 2 := by
    apply (mul_le_mul_iff_right₀ (by positivity : 0 < 4 * K)).mp
    field_simp
    nlinarith only [sq_nonneg (r - 2 * K * (n : ℝ))]
  have hu' : 2 * u + 2 * K * u ^ 2 ≤ (2 * K + 2) * (1 + u) ^ 2 := by
    nlinarith [mul_nonneg hK.le hu, sq_nonneg u]
  calc
    _ ≤ Real.exp ((n : ℝ) * r) * Real.exp ((2 : ℝ) * u) *
        Real.exp (2 * K * u ^ 2 - r ^ 2 / (4 * K)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul (hp r hr n) (hp u hu 2) (by positivity) (Real.exp_pos _).le)
        (Real.exp_pos _).le
    _ = Real.exp ((n : ℝ) * r - r ^ 2 / (4 * K) + (2 * u + 2 * K * u ^ 2)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (add_le_add hy hu')

private lemma gaussian_affine_bound {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (i j : Fin d) (s : ℝ) (hslo : 1 / 2 ≤ s) (ζ : ℂ) (x : Vec d) :
    ‖ζ * (unitVector i j : ℂ) - (((homogenizedCoefficient Q)⁻¹).mulVec x j : ℂ) / (s : ℂ)‖ ≤
      (1 + 2 * sourceReducedBound Λ₀) * (1 + ‖ζ‖) * (1 + euclideanNorm x) := by
  have hs : 0 < s := by linarith
  have hK := reducedBound_pos Q
  have hc : |unitVector i j| ≤ 1 := by
    simp only [unitVector, Pi.single_apply]
    split_ifs <;> norm_num
  have hm := (coord_le_euclideanNorm ((homogenizedCoefficient Q)⁻¹.mulVec x) j).trans
    (homogenizedCoefficient_inv_mulVec_bound Q x)
  have hd : |((homogenizedCoefficient Q)⁻¹).mulVec x j| / s ≤
      2 * sourceReducedBound Λ₀ * euclideanNorm x := by
    apply (div_le_iff₀ hs).mpr
    have hr : 0 ≤ euclideanNorm x := Real.sqrt_nonneg _
    have hh := mul_le_mul_of_nonneg_left hslo
      (show 0 ≤ 2 * sourceReducedBound Λ₀ * euclideanNorm x by positivity)
    linarith
  calc
    _ ≤ ‖ζ * (unitVector i j : ℂ)‖ +
        ‖(((homogenizedCoefficient Q)⁻¹).mulVec x j : ℂ) / (s : ℂ)‖ := norm_sub_le _ _
    _ = ‖ζ‖ * |unitVector i j| + |((homogenizedCoefficient Q)⁻¹).mulVec x j| / s := by
      simp only [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    _ ≤ ‖ζ‖ + 2 * sourceReducedBound Λ₀ * euclideanNorm x :=
      add_le_add (by simpa using mul_le_mul_of_nonneg_left hc (norm_nonneg ζ)) hd
    _ ≤ _ := by
      have hK := (reducedBound_pos Q).le
      have hr : 0 ≤ euclideanNorm x := Real.sqrt_nonneg _
      have hu := norm_nonneg ζ
      nlinarith [mul_nonneg hK hr, mul_nonneg hK hu,
        mul_nonneg hK (mul_nonneg hu hr), mul_nonneg hu hr]

private lemma gaussian_derivative_factor_bounds {K u r : ℝ} (hK : 0 < K)
    (hu : 0 ≤ u) (hr : 0 ≤ r) :
    let H := (1 + 2 * K) ^ 2 + 2 * K + 1
    let a := (1 + 2 * K) * (1 + u) * (1 + r)
    let b := H * (1 + u) ^ 2 * (1 + r) ^ 2
    1 ≤ b ∧ a ≤ b ∧ a ^ 2 + 2 * K ≤ b := by
  dsimp only
  let t := (1 + u) * (1 + r)
  have ht : 1 ≤ t := one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)
  have ht2 : 1 ≤ t ^ 2 := one_le_pow₀ ht
  have htt : t ≤ t ^ 2 := by nlinarith only [ht, sq_nonneg (t - 1)]
  have hF : 1 ≤ 1 + 2 * K := by linarith
  have hF2 : 1 ≤ (1 + 2 * K) ^ 2 := one_le_pow₀ hF
  have hb : ((1 + 2 * K) ^ 2 + 2 * K + 1) * (1 + u) ^ 2 * (1 + r) ^ 2 =
      ((1 + 2 * K) ^ 2 + 2 * K + 1) * t ^ 2 := by dsimp [t]; ring
  rw [hb]
  have ha : (1 + 2 * K) * (1 + u) * (1 + r) = (1 + 2 * K) * t := by dsimp [t]; ring
  rw [ha]
  constructor
  · nlinarith [mul_nonneg (by linarith : 0 ≤ 2 * K + 1) (sub_nonneg.mpr ht2)]
  constructor
  · have hm := mul_le_mul_of_nonneg_left htt (show 0 ≤ 1 + 2 * K by linarith)
    have hh : 1 + 2 * K ≤ (1 + 2 * K) ^ 2 + 2 * K + 1 := by nlinarith
    exact hm.trans (mul_le_mul_of_nonneg_right hh (sq_nonneg t))
  · nlinarith [mul_nonneg (show 0 ≤ 2 * K + 1 by linarith) (sub_nonneg.mpr ht2)]

private lemma gaussian_inverse_entry_div_bound {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (j k : Fin d) (s : ℝ) (hslo : 1 / 2 ≤ s) :
    ‖(((homogenizedCoefficient Q)⁻¹) j k : ℂ) / (s : ℂ)‖ ≤ 2 * sourceReducedBound Λ₀ := by
  have hs : 0 < s := by linarith
  rw [norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos hs]
  apply (div_le_iff₀ hs).mpr
  have hh := mul_le_mul_of_nonneg_left hslo
    (show 0 ≤ 2 * sourceReducedBound Λ₀ by linarith [reducedBound_pos Q])
  linarith [abs_homogenizedCoefficient_inv_entry_le Q j k]

private lemma gaussian_kernel_derivative_domination {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (s : ℝ) (hs : 0 < s)
    (hslo : 1 / 2 ≤ s) (ζ : ℂ) (x : Vec d) :
    let H := (1 + 2 * sourceReducedBound Λ₀) ^ 2 + 2 * sourceReducedBound Λ₀ + 1
    let b := H * (1 + ‖ζ‖) ^ 2 * (1 + euclideanNorm x) ^ 2 *
      ‖homogenizedGaussianKernel Q i s hs ζ x‖
    ‖homogenizedGaussianKernel Q i s hs ζ x‖ ≤ b ∧
      (∀ j, ‖fderiv ℝ (homogenizedGaussianKernel Q i s hs ζ) x (unitVector j)‖ ≤ b) ∧
      (∀ j k, ‖fderiv ℝ (fun y => fderiv ℝ (homogenizedGaussianKernel Q i s hs ζ)
        y (unitVector j)) x (unitVector k)‖ ≤ b) := by
  dsimp only
  have hK := reducedBound_pos Q
  have hr : 0 ≤ euclideanNorm x := Real.sqrt_nonneg _
  obtain ⟨h0, h1, h2⟩ := gaussian_derivative_factor_bounds (reducedBound_pos Q)
    (norm_nonneg ζ) (show 0 ≤ euclideanNorm x from Real.sqrt_nonneg _)
  constructor
  · simpa only [one_mul] using mul_le_mul_of_nonneg_right h0
      (norm_nonneg (homogenizedGaussianKernel Q i s hs ζ x))
  constructor
  · intro j
    rw [fderiv_homogenizedGaussianKernel_complexForce_coordinate, norm_mul]
    exact mul_le_mul_of_nonneg_right ((gaussian_affine_bound Q i j s hslo ζ x).trans h1)
      (norm_nonneg _)
  · intro j k
    rw [fderiv_fderiv_homogenizedGaussianKernel_complexForce_coordinate, norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    calc
      _ ≤ ‖(ζ * (unitVector i j : ℂ) -
          (((homogenizedCoefficient Q)⁻¹).mulVec x j : ℂ) / (s : ℂ)) *
          (ζ * (unitVector i k : ℂ) -
          (((homogenizedCoefficient Q)⁻¹).mulVec x k : ℂ) / (s : ℂ))‖ +
          ‖(((homogenizedCoefficient Q)⁻¹) j k : ℂ) / (s : ℂ)‖ := norm_sub_le _ _
      _ ≤ ((1 + 2 * sourceReducedBound Λ₀) * (1 + ‖ζ‖) *
          (1 + euclideanNorm x)) ^ 2 + 2 * sourceReducedBound Λ₀ := by
        rw [norm_mul, pow_two]
        exact add_le_add (mul_le_mul (gaussian_affine_bound Q i j s hslo ζ x)
          (gaussian_affine_bound Q i k s hslo ζ x) (norm_nonneg _) (by positivity))
          (gaussian_inverse_entry_div_bound Q j k s hslo)
      _ ≤ _ := h2

/-- A fully explicit structural constant for weights and derivatives up to order two.
It is chosen before the law, force, time and spatial point. -/
noncomputable def gaussianSchwartzBound (d : ℕ) (Λ₀ : ℝ) (m : ℕ) : ℝ :=
  let K := sourceReducedBound Λ₀
  let P := Real.sqrt ((Fintype.card (Equiv.Perm (Fin d)) : ℝ) * K ^ d)
  let H := (1 + 2 * K) ^ 2 + 2 * K + 1
  (((d : ℝ) + 1) ^ 2 * (H * P * Real.exp (K * ((m + 2 : ℕ) : ℝ) ^ 2)) + 1) +
    (2 * K + 2) + 1

/-- Positivity of the displayed constant requires only the structural parameter. -/
theorem gaussianSchwartzBound_pos (d : ℕ) (Λ₀ : ℝ) (hΛ : 1 ≤ Λ₀) (m : ℕ) :
    0 < gaussianSchwartzBound d Λ₀ m := by
  have hK : 0 < sourceReducedBound Λ₀ := by
    unfold sourceReducedBound
    exact mul_pos (Real.exp_pos _) (by nlinarith [sq_nonneg Λ₀])
  unfold gaussianSchwartzBound
  positivity

private lemma gaussian_weighted_common_bound {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (s : ℝ) (hs : 0 < s)
    (hslo : 1 / 2 ≤ s) (hshi : s ≤ 1) (ζ : ℂ) (x : Vec d) (m : ℕ) :
    let K := sourceReducedBound Λ₀
    let P := Real.sqrt ((Fintype.card (Equiv.Perm (Fin d)) : ℝ) * K ^ d)
    let H := (1 + 2 * K) ^ 2 + 2 * K + 1
    (1 + euclideanNorm x) ^ m *
      (H * (1 + ‖ζ‖) ^ 2 * (1 + euclideanNorm x) ^ 2 *
        ‖homogenizedGaussianKernel Q i s hs ζ x‖) ≤
      (H * P * Real.exp (K * ((m + 2 : ℕ) : ℝ) ^ 2)) *
        Real.exp ((2 * K + 2) * (1 + ‖ζ‖) ^ 2) := by
  dsimp only
  have hK := reducedBound_pos Q
  have hr : 0 ≤ euclideanNorm x := Real.sqrt_nonneg _
  calc
    _ ≤ (1 + euclideanNorm x) ^ m *
        (((1 + 2 * sourceReducedBound Λ₀) ^ 2 + 2 * sourceReducedBound Λ₀ + 1) *
          (1 + ‖ζ‖) ^ 2 * (1 + euclideanNorm x) ^ 2 *
          (Real.sqrt ((Fintype.card (Equiv.Perm (Fin d)) : ℝ) * sourceReducedBound Λ₀ ^ d) *
            Real.exp (2 * sourceReducedBound Λ₀ * ‖ζ‖ ^ 2 -
              euclideanNorm x ^ 2 / (4 * sourceReducedBound Λ₀)))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (norm_homogenizedGaussianKernel_le_gaussian
          Q i s hs hslo hshi ζ x) (by positivity)) (by positivity)
    _ = (((1 + 2 * sourceReducedBound Λ₀) ^ 2 + 2 * sourceReducedBound Λ₀ + 1) *
        Real.sqrt ((Fintype.card (Equiv.Perm (Fin d)) : ℝ) * sourceReducedBound Λ₀ ^ d)) *
        ((1 + euclideanNorm x) ^ (m + 2) * (1 + ‖ζ‖) ^ 2 *
          Real.exp (2 * sourceReducedBound Λ₀ * ‖ζ‖ ^ 2 -
            euclideanNorm x ^ 2 / (4 * sourceReducedBound Λ₀))) := by
      rw [pow_add]
      ring
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (gaussian_polynomial_absorption hK hr (norm_nonneg ζ) (m + 2)) (by positivity :
          0 ≤ ((1 + 2 * sourceReducedBound Λ₀) ^ 2 + 2 * sourceReducedBound Λ₀ + 1) *
            Real.sqrt ((Fintype.card (Equiv.Perm (Fin d)) : ℝ) * sourceReducedBound Λ₀ ^ d))

/-- Literal weighted pointwise bounds for the kernel and its first two actual
coordinate Fréchet derivatives. This is a deterministic precursor to Schwartz tests. -/
theorem homogenizedGaussianKernel_weighted_coordinate_bounds {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (s : ℝ) (hs : 0 < s)
    (hslo : 1 / 2 ≤ s) (hshi : s ≤ 1) (ζ : ℂ) (x : Vec d) (m : ℕ) :
    let C := gaussianSchwartzBound d Λ₀ m
    (1 + euclideanNorm x) ^ m * ‖homogenizedGaussianKernel Q i s hs ζ x‖ ≤
        C * Real.exp (C * (1 + ‖ζ‖) ^ 2) ∧
      (∀ j, (1 + euclideanNorm x) ^ m *
        ‖fderiv ℝ (homogenizedGaussianKernel Q i s hs ζ) x (unitVector j)‖ ≤
          C * Real.exp (C * (1 + ‖ζ‖) ^ 2)) ∧
      (∀ j k, (1 + euclideanNorm x) ^ m *
        ‖fderiv ℝ (fun y => fderiv ℝ (homogenizedGaussianKernel Q i s hs ζ)
          y (unitVector j)) x (unitVector k)‖ ≤ C * Real.exp (C * (1 + ‖ζ‖) ^ 2)) := by
  dsimp only
  let K := sourceReducedBound Λ₀
  let P := Real.sqrt ((Fintype.card (Equiv.Perm (Fin d)) : ℝ) * K ^ d)
  let H := (1 + 2 * K) ^ 2 + 2 * K + 1
  let A := H * P * Real.exp (K * ((m + 2 : ℕ) : ℝ) ^ 2)
  let E := 2 * K + 2
  have hK : 0 < K := reducedBound_pos Q
  have hA : 0 ≤ A := by dsimp [A, H, P]; positivity
  have hE : 0 ≤ E := by dsimp [E]; linarith
  have hdim : 1 ≤ ((d : ℝ) + 1) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have hAC : A ≤ gaussianSchwartzBound d Λ₀ m := by
    change A ≤ (((d : ℝ) + 1) ^ 2 * A + 1) + E + 1
    nlinarith [mul_le_mul_of_nonneg_right hdim hA]
  have hEC : E ≤ gaussianSchwartzBound d Λ₀ m := by
    change E ≤ (((d : ℝ) + 1) ^ 2 * A + 1) + E + 1
    nlinarith [mul_nonneg (sq_nonneg ((d : ℝ) + 1)) hA]
  have hcommon := (gaussian_weighted_common_bound Q i s hs hslo hshi ζ x m).trans
    (mul_le_mul hAC (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hEC (sq_nonneg _)))
      (Real.exp_pos _).le ((gaussianSchwartzBound_pos d Λ₀ Q.ellipticity_parameter m).le))
  obtain ⟨h0, h1, h2⟩ := gaussian_kernel_derivative_domination Q i s hs hslo ζ x
  have hw : 0 ≤ (1 + euclideanNorm x) ^ m := by
    have hr : 0 ≤ euclideanNorm x := Real.sqrt_nonneg _
    positivity
  exact ⟨(mul_le_mul_of_nonneg_left h0 hw).trans hcommon,
    (fun j => (mul_le_mul_of_nonneg_left (h1 j) hw).trans hcommon),
    (fun j k => (mul_le_mul_of_nonneg_left (h2 j k) hw).trans hcommon)⟩

private lemma clm_apply_coordinate_sum (L : Vec d →L[ℝ] ℂ) (v : Vec d) :
    L v = ∑ j, (v j : ℂ) * L (unitVector j) := by
  have hv : v = ∑ j, v j • unitVector j := by
    ext k
    simp [unitVector, Pi.single_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_ite]
  conv_lhs => rw [hv, map_sum]
  simp only [map_smul, Complex.real_smul]

private lemma weighted_coordinate_sum_bound (F : Fin d → ℂ) {W B : ℝ}
    (hW : 0 ≤ W) (hF : ∀ j, W * ‖F j‖ ≤ B) (v : Vec d) :
    W * ‖∑ j, (v j : ℂ) * F j‖ ≤ (d : ℝ) * B * euclideanNorm v := by
  calc
    _ ≤ W * ∑ j, ‖(v j : ℂ) * F j‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) hW
    _ = ∑ j, |v j| * (W * ‖F j‖) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      ring
    _ ≤ ∑ _j : Fin d, euclideanNorm v * B := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul (coord_le_euclideanNorm v j) (hF j)
        (mul_nonneg hW (norm_nonneg _)) (Real.sqrt_nonneg _)
    _ = _ := by simp; ring

/-- The full first and mixed second real spatial derivatives satisfy the same
uniform weighted bounds in arbitrary Euclidean directions. In particular this
applies literally at time one and at half time, for all signed complex forces.
No Schwartz-map packaging or stochastic covariance replacement is asserted. -/
theorem homogenizedGaussianKernel_weighted_fderiv_bounds {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (s : ℝ) (hs : 0 < s)
    (hslo : 1 / 2 ≤ s) (hshi : s ≤ 1) (ζ : ℂ) (x : Vec d) (m : ℕ) :
    let C := ((d : ℝ) + 1) ^ 2 * gaussianSchwartzBound d Λ₀ m
    (1 + euclideanNorm x) ^ m * ‖homogenizedGaussianKernel Q i s hs ζ x‖ ≤
        C * Real.exp (C * (1 + ‖ζ‖) ^ 2) ∧
      (∀ v : Vec d, (1 + euclideanNorm x) ^ m *
        ‖fderiv ℝ (homogenizedGaussianKernel Q i s hs ζ) x v‖ ≤
          C * Real.exp (C * (1 + ‖ζ‖) ^ 2) * euclideanNorm v) ∧
      (∀ v w : Vec d, (1 + euclideanNorm x) ^ m *
        ‖fderiv ℝ (fun y => fderiv ℝ (homogenizedGaussianKernel Q i s hs ζ) y v) x w‖ ≤
          C * Real.exp (C * (1 + ‖ζ‖) ^ 2) * euclideanNorm v * euclideanNorm w) := by
  dsimp only
  let C₀ := gaussianSchwartzBound d Λ₀ m
  let D := ((d : ℝ) + 1) ^ 2
  let C := D * C₀
  let B := C₀ * Real.exp (C₀ * (1 + ‖ζ‖) ^ 2)
  have hC₀ : 0 < C₀ := gaussianSchwartzBound_pos d Λ₀ Q.ellipticity_parameter m
  have hB : 0 ≤ B := mul_nonneg hC₀.le (Real.exp_pos _).le
  have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hD : 1 ≤ D := by dsimp [D]; nlinarith
  have hdD : (d : ℝ) ≤ D := by dsimp [D]; nlinarith
  have hd2D : (d : ℝ) ^ 2 ≤ D := by dsimp [D]; nlinarith
  have hC : C₀ ≤ C := le_mul_of_one_le_left hC₀.le hD
  have hlarge : D * B ≤ C * Real.exp (C * (1 + ‖ζ‖) ^ 2) := by
    change D * (C₀ * Real.exp _) ≤ (D * C₀) * Real.exp _
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hC (sq_nonneg _)))
      (mul_nonneg (le_trans (by norm_num) hD) hC₀.le)
  have hBlarge : B ≤ C * Real.exp (C * (1 + ‖ζ‖) ^ 2) :=
    (le_mul_of_one_le_left hB hD).trans hlarge
  have hdBlarge : (d : ℝ) * B ≤ C * Real.exp (C * (1 + ‖ζ‖) ^ 2) :=
    (mul_le_mul_of_nonneg_right hdD hB).trans hlarge
  have hd2Blarge : (d : ℝ) ^ 2 * B ≤ C * Real.exp (C * (1 + ‖ζ‖) ^ 2) :=
    (mul_le_mul_of_nonneg_right hd2D hB).trans hlarge
  obtain ⟨h0, h1, h2⟩ := homogenizedGaussianKernel_weighted_coordinate_bounds
    Q i s hs hslo hshi ζ x m
  have hw : 0 ≤ (1 + euclideanNorm x) ^ m := by
    have hr : 0 ≤ euclideanNorm x := Real.sqrt_nonneg _
    positivity
  refine ⟨h0.trans hBlarge, ?_, ?_⟩
  · intro v
    rw [clm_apply_coordinate_sum]
    exact (weighted_coordinate_sum_bound _ hw h1 v).trans
      (mul_le_mul_of_nonneg_right hdBlarge (Real.sqrt_nonneg _))
  · intro v w
    have heq : fderiv ℝ (fun y => fderiv ℝ (homogenizedGaussianKernel Q i s hs ζ) y v) x w =
        ∑ j, (v j : ℂ) * (∑ k, (w k : ℂ) *
          fderiv ℝ (fun y => fderiv ℝ (homogenizedGaussianKernel Q i s hs ζ)
            y (unitVector j)) x (unitVector k)) := by
      rw [fderiv_fderiv_homogenizedGaussianKernel_complexForce_apply]
      simp_rw [fderiv_fderiv_homogenizedGaussianKernel_complexForce_coordinate]
      simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [heq]
    have hh := weighted_coordinate_sum_bound _ hw
      (fun j => weighted_coordinate_sum_bound _ hw (h2 j) w) v
    calc
      _ ≤ (d : ℝ) * ((d : ℝ) * B * euclideanNorm w) * euclideanNorm v := hh
      _ = ((d : ℝ) ^ 2 * B) * euclideanNorm v * euclideanNorm w := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hd2Blarge (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

/-- One structural witness works before every law, complex force and spatial point,
for every polynomial weight and derivatives of orders zero, one and two.
The displayed definition `gaussianSchwartzBound` supplies an explicit witness. -/
theorem exists_uniform_gaussian_weighted_fderiv_bounds (d : ℕ) (Λ₀ : ℝ)
    (hΛ : 1 ≤ Λ₀) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
      (s : ℝ) (hs : 0 < s), 1 / 2 ≤ s → s ≤ 1 → ∀ (ζ : ℂ) (x : Vec d),
      (1 + euclideanNorm x) ^ m * ‖homogenizedGaussianKernel Q i s hs ζ x‖ ≤
          C * Real.exp (C * (1 + ‖ζ‖) ^ 2) ∧
        (∀ v : Vec d, (1 + euclideanNorm x) ^ m *
          ‖fderiv ℝ (homogenizedGaussianKernel Q i s hs ζ) x v‖ ≤
            C * Real.exp (C * (1 + ‖ζ‖) ^ 2) * euclideanNorm v) ∧
        (∀ v w : Vec d, (1 + euclideanNorm x) ^ m *
          ‖fderiv ℝ (fun y => fderiv ℝ (homogenizedGaussianKernel Q i s hs ζ) y v) x w‖ ≤
            C * Real.exp (C * (1 + ‖ζ‖) ^ 2) * euclideanNorm v * euclideanNorm w) := by
  refine ⟨((d : ℝ) + 1) ^ 2 * gaussianSchwartzBound d Λ₀ m,
    mul_pos (sq_pos_of_pos (by positivity)) (gaussianSchwartzBound_pos d Λ₀ hΛ m), ?_⟩
  intro r₀ Q i s hs hslo hshi ζ x
  exact homogenizedGaussianKernel_weighted_fderiv_bounds Q i s hs hslo hshi ζ x m


private lemma norm_iteratedFDeriv_affine {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : E →L[ℝ] F) (b : F) (x : E) {B : ℝ} (hB : 1 ≤ B)
    (h0 : ‖b + T x‖ ≤ B) (h1 : ‖T‖ ≤ B) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun y => b + T y) x‖ ≤ B ^ (n + 1) := by
  cases n with
  | zero => simpa only [norm_iteratedFDeriv_zero, Nat.zero_add, pow_one] using h0
  | succ n =>
    have heq : fderiv ℝ (fun y => b + T y) = fun _ => T := by
      ext y
      rw [fderiv_const_add, T.fderiv]
    rw [← norm_iteratedFDeriv_fderiv, heq]
    cases n with
    | zero =>
      rw [norm_iteratedFDeriv_zero]
      exact h1.trans (le_self_pow₀ hB (by omega))
    | succ n =>
      rw [iteratedFDeriv_succ_const]
      simp only [Pi.zero_apply, norm_zero]
      exact pow_nonneg (le_trans (by norm_num) hB) _

private lemma norm_iteratedFDeriv_affine_log {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℂ) (T : E →L[ℝ] (E →L[ℝ] ℂ)) (b : E →L[ℝ] ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hdf : fderiv ℝ f = fun y => f y • (b + T y))
    (x : E) {B : ℝ} (hB : 1 ≤ B) (h0 : ‖b + T x‖ ≤ B) (h1 : ‖T‖ ≤ B)
    (n : ℕ) :
    ‖iteratedFDeriv ℝ n f x‖ ≤ (2 : ℝ) ^ (n ^ 2) * B ^ n * ‖f x‖ := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [norm_iteratedFDeriv_zero]
    | succ n =>
      rw [← norm_iteratedFDeriv_fderiv, hdf]
      have hsum := norm_iteratedFDeriv_smul_le hf
        ((contDiff_const (c := b)).add T.contDiff) x (n := n) (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
      apply hsum.trans
      calc
        _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
            ((2 : ℝ) ^ (n ^ 2) * B ^ i * ‖f x‖) * B ^ (n - i + 1) := by
          apply Finset.sum_le_sum
          intro i hi
          have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
          have hpow : (2 : ℝ) ^ (i ^ 2) ≤ 2 ^ (n ^ 2) :=
            pow_le_pow_right₀ (by norm_num) (Nat.pow_le_pow_left hin 2)
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left
              ((ih i (by omega)).trans (by gcongr)) (Nat.cast_nonneg _)
          · exact norm_iteratedFDeriv_affine T b x hB h0 h1 _
          · exact norm_nonneg _
          · positivity
        _ = (2 : ℝ) ^ n * (2 ^ (n ^ 2) * B ^ (n + 1) * ‖f x‖) := by
          have hi (i : ℕ) (hi : i ∈ Finset.range (n + 1)) :
              (n.choose i : ℝ) * (2 ^ (n ^ 2) * B ^ i * ‖f x‖) * B ^ (n - i + 1) =
                (n.choose i : ℝ) * (2 ^ (n ^ 2) * B ^ (n + 1) * ‖f x‖) := by
            have hie : i + (n - i + 1) = n + 1 := by
              have := Finset.mem_range.mp hi
              omega
            rw [show (n.choose i : ℝ) * (2 ^ (n ^ 2) * B ^ i * ‖f x‖) * B ^ (n - i + 1) =
              (n.choose i : ℝ) * (2 ^ (n ^ 2) * (B ^ i * B ^ (n - i + 1)) * ‖f x‖) by ring,
              ← pow_add, hie]
          rw [Finset.sum_congr rfl hi, ← Finset.sum_mul]
          congr 1
          exact_mod_cast Nat.sum_range_choose n
        _ ≤ _ := by
          rw [show (2 : ℝ) ^ n * (2 ^ (n ^ 2) * B ^ (n + 1) * ‖f x‖) =
            2 ^ (n + n ^ 2) * B ^ (n + 1) * ‖f x‖ by rw [pow_add]; ring]
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by linarith : 0 ≤ B) _)
          apply pow_le_pow_right₀ (by norm_num)
          nlinarith


private noncomputable def complexCoordinate (j : Fin d) : Vec d →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (ContinuousLinearMap.proj j)

private lemma norm_complexCoordinate_le (j : Fin d) : ‖complexCoordinate j‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  simpa only [complexCoordinate, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, Complex.ofRealCLM_apply, Complex.norm_real,
    one_mul] using norm_le_pi_norm x j

private noncomputable def coordinateTensor (j k : Fin d) (c : ℂ) :
    Vec d →L[ℝ] (Vec d →L[ℝ] ℂ) :=
  (ContinuousLinearMap.proj k : Vec d →L[ℝ] ℝ).smulRight (c • complexCoordinate j)

private noncomputable def gaussianLogGradientLinear (B : Mat d) (s : ℝ) :
    Vec d →L[ℝ] (Vec d →L[ℝ] ℂ) :=
  ∑ j, ∑ k, coordinateTensor j k (-((B j k : ℝ) : ℂ) / (s : ℂ))

private lemma norm_coordinate_tensor_le (j k : Fin d) (c : ℂ) :
    ‖coordinateTensor j k c‖ ≤ ‖c‖ := by
  unfold coordinateTensor
  have hp : ‖(ContinuousLinearMap.proj k : Vec d →L[ℝ] ℝ)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro x
    simpa only [ContinuousLinearMap.proj_apply, one_mul] using norm_le_pi_norm x k
  rw [ContinuousLinearMap.norm_smulRight_apply, norm_smul]
  calc
    _ ≤ 1 * (‖c‖ * 1) := mul_le_mul hp
      (mul_le_mul_of_nonneg_left (norm_complexCoordinate_le j) (norm_nonneg c))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num)
    _ = _ := by ring

private lemma norm_fin_double_sum_le {F : Type*} [SeminormedAddCommGroup F]
    (a : Fin d → Fin d → F) (M : ℝ) (ha : ∀ j k, ‖a j k‖ ≤ M) :
    ‖∑ j, ∑ k, a j k‖ ≤ (d : ℝ) ^ 2 * M := by
  calc
    _ ≤ ∑ j, ∑ k, ‖a j k‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => norm_sum_le _ _))
    _ ≤ ∑ _j : Fin d, ∑ _k : Fin d, M :=
      Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ => ha j k))
    _ = _ := by simp; ring

private lemma norm_gaussianLogGradientLinear_le (B : Mat d) (s M : ℝ)
    (hB : ∀ j k, ‖((B j k : ℝ) : ℂ) / (s : ℂ)‖ ≤ M) :
    ‖gaussianLogGradientLinear B s‖ ≤ (d : ℝ) ^ 2 * M := by
  have ht (j k : Fin d) :
      ‖coordinateTensor j k (-((B j k : ℝ) : ℂ) / (s : ℂ))‖ ≤ M := by
    apply (norm_coordinate_tensor_le j k _).trans
    simpa only [neg_div, norm_neg] using hB j k
  exact norm_fin_double_sum_le
    (fun j k => coordinateTensor j k (-((B j k : ℝ) : ℂ) / (s : ℂ))) M ht

private lemma fderiv_eq_logGradient {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) (s : ℝ) (hs : 0 < s) (ζ : ℂ) :
    fderiv ℝ (homogenizedGaussianKernel Q i s hs ζ) = fun x =>
      homogenizedGaussianKernel Q i s hs ζ x •
        (ζ • complexCoordinate i + gaussianLogGradientLinear (homogenizedCoefficient Q)⁻¹ s x) := by
  ext x v
  rw [fderiv_homogenizedGaussianKernel_complexForce_apply]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul,
    ContinuousLinearMap.add_apply, complexCoordinate, gaussianLogGradientLinear, coordinateTensor,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply,
    Complex.ofRealCLM_apply, Complex.real_smul, Matrix.mulVec, dotProduct,
    Complex.ofReal_sum, Complex.ofReal_mul]
  simp only [Finset.sum_sub_distrib, mul_sub]
  have hc : ∑ j, (v j : ℂ) * (ζ * (unitVector i j : ℂ)) = ζ * (v i : ℂ) := by
    simp [unitVector, Pi.single_apply, apply_ite Complex.ofReal, mul_ite, mul_comm]
  rw [hc]
  simp only [Finset.sum_div, Finset.mul_sum, neg_div, mul_neg, neg_mul,
    Finset.sum_neg_distrib]
  have he : (∑ j, ∑ k, (v j : ℂ) *
      (((homogenizedCoefficient Q)⁻¹ j k : ℂ) * (x k : ℂ) / (s : ℂ))) =
      ∑ j, ∑ k, (x k : ℂ) *
        (((homogenizedCoefficient Q)⁻¹ j k : ℂ) / (s : ℂ) * (v j : ℂ)) := by
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he]
  ring


/-- The coordinate carrier's function norm is bounded by the explicit Euclidean norm. -/
theorem norm_vec_le_euclideanNorm (x : Vec d) : ‖x‖ ≤ euclideanNorm x := by
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
  intro j
  rw [Real.norm_eq_abs]
  apply le_of_sq_le_sq _ (Real.sqrt_nonneg _)
  change |x j| ^ 2 ≤ Real.sqrt (euclideanSq x) ^ 2
  have hsq : 0 ≤ euclideanSq x := by
    unfold euclideanSq dot
    exact Finset.sum_nonneg (fun k _ => mul_self_nonneg (x k))
  rw [sq_abs, Real.sq_sqrt hsq]
  simpa only [euclideanSq, dot, pow_two] using
    Finset.single_le_sum (fun k _ => mul_self_nonneg (x k)) (Finset.mem_univ j)

private lemma affine_log_gradient_bound {u r F : ℝ} (hu : 0 ≤ u) (hr : 0 ≤ r)
    (hF : 1 ≤ F) : u + F * r ≤ F * (1 + u) * (1 + r) := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hF) hu,
    mul_nonneg (le_trans (by norm_num) hF) (mul_nonneg hu hr)]

/-- All real spatial derivative orders of the literal kernel are bounded by a
polynomial times its actual complex norm. The operator norm here is for the
coordinate carrier; direction estimates are transported explicitly below. -/
theorem norm_iteratedFDeriv_homogenizedGaussianKernel_le {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (s : ℝ) (hs : 0 < s)
    (hslo : 1 / 2 ≤ s) (ζ : ℂ) (x : Vec d) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (homogenizedGaussianKernel Q i s hs ζ) x‖ ≤
      (2 : ℝ) ^ (n ^ 2) *
        ((1 + 2 * (d : ℝ) ^ 2 * sourceReducedBound Λ₀) *
          (1 + ‖ζ‖) * (1 + euclideanNorm x)) ^ n *
        ‖homogenizedGaussianKernel Q i s hs ζ x‖ := by
  let T := gaussianLogGradientLinear (homogenizedCoefficient Q)⁻¹ s
  let F := 1 + 2 * (d : ℝ) ^ 2 * sourceReducedBound Λ₀
  let B := F * (1 + ‖ζ‖) * (1 + euclideanNorm x)
  have hK : 0 < sourceReducedBound Λ₀ := by
    unfold sourceReducedBound
    exact mul_pos (Real.exp_pos _) (by nlinarith [Q.ellipticity_parameter, sq_nonneg Λ₀])
  have hF : 1 ≤ F := by
    dsimp [F]
    have : 0 ≤ 2 * (d : ℝ) ^ 2 * sourceReducedBound Λ₀ := by positivity
    linarith
  have hr : 0 ≤ euclideanNorm x := Real.sqrt_nonneg _
  have hB : 1 ≤ B := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hF (by linarith [norm_nonneg ζ])) (by linarith)
  have hTF : ‖T‖ ≤ F := by
    have hentry (j k : Fin d) :
        ‖(((homogenizedCoefficient Q)⁻¹ j k : ℝ) : ℂ) / (s : ℂ)‖ ≤
          2 * sourceReducedBound Λ₀ := by
      rw [norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_pos hs]
      apply (div_le_iff₀ hs).mpr
      have hh := mul_le_mul_of_nonneg_left hslo (by positivity : 0 ≤ 2 * sourceReducedBound Λ₀)
      linarith [abs_homogenizedCoefficient_inv_entry_le Q j k]
    have hh := norm_gaussianLogGradientLinear_le (homogenizedCoefficient Q)⁻¹ s
      (2 * sourceReducedBound Λ₀) hentry
    change ‖T‖ ≤ _ at hh
    dsimp [F]
    nlinarith
  have h1 : ‖T‖ ≤ B := hTF.trans (by
    calc
      F ≤ F * (1 + ‖ζ‖) :=
        le_mul_of_one_le_right (by linarith) (by linarith [norm_nonneg ζ])
      _ ≤ B := le_mul_of_one_le_right (by positivity) (by linarith))
  have h0 : ‖ζ • complexCoordinate i + T x‖ ≤ B := by
    calc
      _ ≤ ‖ζ • complexCoordinate i‖ + ‖T x‖ := norm_add_le _ _
      _ ≤ ‖ζ‖ + F * euclideanNorm x := by
        apply add_le_add
        · rw [norm_smul]
          exact (mul_le_mul_of_nonneg_left (norm_complexCoordinate_le i) (norm_nonneg ζ)).trans
            (by simp)
        · exact (T.le_opNorm x).trans (mul_le_mul hTF (norm_vec_le_euclideanNorm x)
            (norm_nonneg _) (by linarith))
      _ ≤ B := affine_log_gradient_bound (norm_nonneg ζ) hr hF
  exact norm_iteratedFDeriv_affine_log _ T (ζ • complexCoordinate i)
    (contDiff_homogenizedGaussianKernel_complexForce Q i s hs ζ)
    (fderiv_eq_logGradient Q i s hs ζ) x hB h0 h1 n


private lemma gaussian_polynomial_absorption_order {K r u : ℝ} (hK : 0 < K)
    (hr : 0 ≤ r) (hu : 0 ≤ u) (p n : ℕ) :
    (1 + r) ^ p * (1 + u) ^ n * Real.exp (2 * K * u ^ 2 - r ^ 2 / (4 * K)) ≤
      Real.exp (K * (p : ℝ) ^ 2) * Real.exp ((2 * K + n) * (1 + u) ^ 2) := by
  have hp (t : ℝ) (ht : 0 ≤ t) (m : ℕ) : (1 + t) ^ m ≤ Real.exp ((m : ℝ) * t) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp t]) m
  have hy : (p : ℝ) * r - r ^ 2 / (4 * K) ≤ K * (p : ℝ) ^ 2 := by
    apply (mul_le_mul_iff_right₀ (by positivity : 0 < 4 * K)).mp
    field_simp
    nlinarith only [sq_nonneg (r - 2 * K * (p : ℝ))]
  have hu' : (n : ℝ) * u + 2 * K * u ^ 2 ≤ (2 * K + n) * (1 + u) ^ 2 := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith [mul_nonneg hK.le hu, mul_nonneg hn hu, mul_nonneg hn (sq_nonneg u)]
  calc
    _ ≤ Real.exp ((p : ℝ) * r) * Real.exp ((n : ℝ) * u) *
        Real.exp (2 * K * u ^ 2 - r ^ 2 / (4 * K)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul (hp r hr p) (hp u hu n) (by positivity) (Real.exp_pos _).le)
        (Real.exp_pos _).le
    _ = Real.exp ((p : ℝ) * r - r ^ 2 / (4 * K) + ((n : ℝ) * u + 2 * K * u ^ 2)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (add_le_add hy hu')

/-- Explicit structural bound for spatial derivative order `n` and weight `m`.
It is chosen before the law, time, complex force and spatial point. -/
noncomputable def gaussianSchwartzOrderBound (d : ℕ) (Λ₀ : ℝ) (m n : ℕ) : ℝ :=
  let K := sourceReducedBound Λ₀
  let P := Real.sqrt ((Fintype.card (Equiv.Perm (Fin d)) : ℝ) * K ^ d)
  (2 ^ (n ^ 2) * (1 + 2 * (d : ℝ) ^ 2 * K) ^ n * P *
    Real.exp (K * ((m + n : ℕ) : ℝ) ^ 2) + 1) + (2 * K + n) + 1

theorem gaussianSchwartzOrderBound_pos (d : ℕ) (Λ₀ : ℝ) (hΛ : 1 ≤ Λ₀)
    (m n : ℕ) : 0 < gaussianSchwartzOrderBound d Λ₀ m n := by
  have hK : 0 < sourceReducedBound Λ₀ := by
    unfold sourceReducedBound
    exact mul_pos (Real.exp_pos _) (by nlinarith [sq_nonneg Λ₀])
  unfold gaussianSchwartzOrderBound
  positivity

/-- Every weighted real spatial Fréchet derivative of the literal complex-force
kernel has a uniform structural bound. The spatial weight uses Euclidean norm;
the multilinear operator norm on the coordinate carrier is also controlled. -/
theorem homogenizedGaussianKernel_weighted_iteratedFDeriv_bound {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (s : ℝ) (hs : 0 < s)
    (hslo : 1 / 2 ≤ s) (hshi : s ≤ 1) (ζ : ℂ) (x : Vec d) (m n : ℕ) :
    let C := gaussianSchwartzOrderBound d Λ₀ m n
    (1 + euclideanNorm x) ^ m *
        ‖iteratedFDeriv ℝ n (homogenizedGaussianKernel Q i s hs ζ) x‖ ≤
      C * Real.exp (C * (1 + ‖ζ‖) ^ 2) := by
  let K := sourceReducedBound Λ₀
  let P := Real.sqrt ((Fintype.card (Equiv.Perm (Fin d)) : ℝ) * K ^ d)
  let F := 1 + 2 * (d : ℝ) ^ 2 * K
  let A := (2 : ℝ) ^ (n ^ 2) * F ^ n * P * Real.exp (K * ((m + n : ℕ) : ℝ) ^ 2)
  let E := 2 * K + n
  let C := gaussianSchwartzOrderBound d Λ₀ m n
  have hK : 0 < K := reducedBound_pos Q
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hP : 0 ≤ P := Real.sqrt_nonneg _
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hAC : A ≤ C := by
    change A ≤ (A + 1) + E + 1
    linarith
  have hEC : E ≤ C := by
    change E ≤ (A + 1) + E + 1
    linarith
  have hC : 0 ≤ C := (gaussianSchwartzOrderBound_pos d Λ₀ Q.ellipticity_parameter m n).le
  have hr : 0 ≤ euclideanNorm x := Real.sqrt_nonneg _
  have hw : 0 ≤ (1 + euclideanNorm x) ^ m := by positivity
  have hd := norm_iteratedFDeriv_homogenizedGaussianKernel_le Q i s hs hslo ζ x n
  have hg := norm_homogenizedGaussianKernel_le_gaussian Q i s hs hslo hshi ζ x
  have hc : (1 + euclideanNorm x) ^ m *
      ‖iteratedFDeriv ℝ n (homogenizedGaussianKernel Q i s hs ζ) x‖ ≤
      A * Real.exp (E * (1 + ‖ζ‖) ^ 2) := by
    calc
      _ ≤ (1 + euclideanNorm x) ^ m *
          ((2 : ℝ) ^ (n ^ 2) * (F * (1 + ‖ζ‖) * (1 + euclideanNorm x)) ^ n *
            (P * Real.exp (2 * K * ‖ζ‖ ^ 2 - euclideanNorm x ^ 2 / (4 * K)))) := by
        apply mul_le_mul_of_nonneg_left _ hw
        exact hd.trans (mul_le_mul_of_nonneg_left hg (by positivity))
      _ = ((2 : ℝ) ^ (n ^ 2) * F ^ n * P) *
          ((1 + euclideanNorm x) ^ (m + n) * (1 + ‖ζ‖) ^ n *
            Real.exp (2 * K * ‖ζ‖ ^ 2 - euclideanNorm x ^ 2 / (4 * K))) := by
        rw [pow_add]
        simp only [mul_pow]
        ring
      _ ≤ ((2 : ℝ) ^ (n ^ 2) * F ^ n * P) *
          (Real.exp (K * ((m + n : ℕ) : ℝ) ^ 2) *
            Real.exp (E * (1 + ‖ζ‖) ^ 2)) := by
        exact mul_le_mul_of_nonneg_left
          (gaussian_polynomial_absorption_order hK hr (norm_nonneg ζ) (m + n) n) (by positivity)
      _ = _ := by dsimp [A]; ring
  exact hc.trans (mul_le_mul hAC
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hEC (sq_nonneg _)))
    (Real.exp_pos _).le hC)

/-- The same structural bound controls all Euclidean direction evaluations of
any iterated real spatial derivative. -/
theorem homogenizedGaussianKernel_weighted_iteratedFDeriv_apply_bound {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (s : ℝ) (hs : 0 < s)
    (hslo : 1 / 2 ≤ s) (hshi : s ≤ 1) (ζ : ℂ) (x : Vec d) (m n : ℕ)
    (v : Fin n → Vec d) :
    let C := gaussianSchwartzOrderBound d Λ₀ m n
    (1 + euclideanNorm x) ^ m *
        ‖iteratedFDeriv ℝ n (homogenizedGaussianKernel Q i s hs ζ) x v‖ ≤
      C * Real.exp (C * (1 + ‖ζ‖) ^ 2) * ∏ j, euclideanNorm (v j) := by
  let L := iteratedFDeriv ℝ n (homogenizedGaussianKernel Q i s hs ζ) x
  have hW : 0 ≤ (1 + euclideanNorm x) ^ m := by
    have := Real.sqrt_nonneg (euclideanSq x)
    positivity
  calc
    _ ≤ (1 + euclideanNorm x) ^ m * (‖L‖ * ∏ j, ‖v j‖) :=
      mul_le_mul_of_nonneg_left (L.le_opNorm v) hW
    _ = ((1 + euclideanNorm x) ^ m * ‖L‖) * ∏ j, ‖v j‖ := by ring
    _ ≤ (gaussianSchwartzOrderBound d Λ₀ m n *
        Real.exp (gaussianSchwartzOrderBound d Λ₀ m n * (1 + ‖ζ‖) ^ 2)) *
          ∏ j, euclideanNorm (v j) := by
      apply mul_le_mul
      · exact homogenizedGaussianKernel_weighted_iteratedFDeriv_bound Q i s hs hslo hshi ζ x m n
      · exact Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) (fun j _ => norm_vec_le_euclideanNorm _)
      · exact Finset.prod_nonneg (fun j _ => norm_nonneg _)
      · exact mul_nonneg (gaussianSchwartzOrderBound_pos d Λ₀ Q.ellipticity_parameter m n).le
          (Real.exp_pos _).le


/-- A single explicit structural witness precedes the law, time, force and point,
for arbitrary polynomial weight and arbitrary real spatial derivative order. -/
theorem exists_uniform_gaussian_weighted_iteratedFDeriv_bounds (d : ℕ) (Λ₀ : ℝ)
    (hΛ : 1 ≤ Λ₀) (m n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
      (s : ℝ) (hs : 0 < s), 1 / 2 ≤ s → s ≤ 1 → ∀ (ζ : ℂ) (x : Vec d),
      (1 + euclideanNorm x) ^ m *
          ‖iteratedFDeriv ℝ n (homogenizedGaussianKernel Q i s hs ζ) x‖ ≤
        C * Real.exp (C * (1 + ‖ζ‖) ^ 2) ∧
      ∀ v : Fin n → Vec d, (1 + euclideanNorm x) ^ m *
          ‖iteratedFDeriv ℝ n (homogenizedGaussianKernel Q i s hs ζ) x v‖ ≤
        C * Real.exp (C * (1 + ‖ζ‖) ^ 2) * ∏ j, euclideanNorm (v j) := by
  refine ⟨gaussianSchwartzOrderBound d Λ₀ m n,
    gaussianSchwartzOrderBound_pos d Λ₀ hΛ m n, ?_⟩
  intro r₀ Q i s hs hslo hshi ζ x
  exact ⟨homogenizedGaussianKernel_weighted_iteratedFDeriv_bound Q i s hs hslo hshi ζ x m n,
    homogenizedGaussianKernel_weighted_iteratedFDeriv_apply_bound Q i s hs hslo hshi ζ x m n⟩

private lemma gaussianSchwartz_seminorm_pointwise_bound {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (s : ℝ) (hs : 0 < s)
    (hslo : 1 / 2 ≤ s) (hshi : s ≤ 1) (ζ : ℂ) (x : Vec d) (m n : ℕ) :
    let C := gaussianSchwartzOrderBound d Λ₀ m n
    ‖x‖ ^ m * ‖iteratedFDeriv ℝ n (homogenizedGaussianKernel Q i s hs ζ) x‖ ≤
      C * Real.exp (C * (1 + ‖ζ‖) ^ 2) := by
  have hx : ‖x‖ ≤ 1 + euclideanNorm x := (norm_vec_le_euclideanNorm x).trans (by linarith)
  exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg x) hx m)
    (norm_nonneg _)).trans
    (homogenizedGaussianKernel_weighted_iteratedFDeriv_bound Q i s hs hslo hshi ζ x m n)

/-- The literal anisotropic complex-force kernel as a Schwartz test function on
its existing coordinate carrier. Euclidean weighted derivative bounds above
supply decay via the proved comparison `norm_vec_le_euclideanNorm`. -/
noncomputable def homogenizedGaussianSchwartz {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (s : ℝ) (hs : 0 < s)
    (hslo : 1 / 2 ≤ s) (hshi : s ≤ 1) (ζ : ℂ) : SchwartzMap (Vec d) ℂ where
  toFun := homogenizedGaussianKernel Q i s hs ζ
  smooth' := contDiff_homogenizedGaussianKernel_complexForce Q i s hs ζ
  decay' m n := ⟨gaussianSchwartzOrderBound d Λ₀ m n *
    Real.exp (gaussianSchwartzOrderBound d Λ₀ m n * (1 + ‖ζ‖) ^ 2),
    fun x => gaussianSchwartz_seminorm_pointwise_bound Q i s hs hslo hshi ζ x m n⟩

@[simp] theorem homogenizedGaussianSchwartz_apply {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (s : ℝ) (hs : 0 < s)
    (hslo : 1 / 2 ≤ s) (hshi : s ≤ 1) (ζ : ℂ) (x : Vec d) :
    homogenizedGaussianSchwartz Q i s hs hslo hshi ζ x =
      homogenizedGaussianKernel Q i s hs ζ x := rfl

/-- The actual Mathlib Schwartz seminorm, with its norm conventions explicitly
compared above, obeys the same structural bound for every weight and order. -/
theorem seminorm_homogenizedGaussianSchwartz_le {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (s : ℝ) (hs : 0 < s)
    (hslo : 1 / 2 ≤ s) (hshi : s ≤ 1) (ζ : ℂ) (m n : ℕ) :
    let C := gaussianSchwartzOrderBound d Λ₀ m n
    SchwartzMap.seminorm ℂ m n (homogenizedGaussianSchwartz Q i s hs hslo hshi ζ) ≤
      C * Real.exp (C * (1 + ‖ζ‖) ^ 2) := by
  apply SchwartzMap.seminorm_le_bound ℂ m n _
    (mul_nonneg (gaussianSchwartzOrderBound_pos d Λ₀ Q.ellipticity_parameter m n).le
      (Real.exp_pos _).le)
  intro x
  exact gaussianSchwartz_seminorm_pointwise_bound Q i s hs hslo hshi ζ x m n

/-- Uniform Schwartz-test bounds with the witness chosen before the actual
law and all force, space and time variables. This includes time one and half time. -/
theorem exists_uniform_homogenizedGaussianSchwartz_seminorm_bound (d : ℕ) (Λ₀ : ℝ)
    (hΛ : 1 ≤ Λ₀) (m n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
      (s : ℝ) (hs : 0 < s) (hslo : 1 / 2 ≤ s) (hshi : s ≤ 1) (ζ : ℂ),
      SchwartzMap.seminorm ℂ m n (homogenizedGaussianSchwartz Q i s hs hslo hshi ζ) ≤
        C * Real.exp (C * (1 + ‖ζ‖) ^ 2) := by
  exact ⟨gaussianSchwartzOrderBound d Λ₀ m n, gaussianSchwartzOrderBound_pos d Λ₀ hΛ m n,
    fun _ Q i s hs hslo hshi ζ => seminorm_homogenizedGaussianSchwartz_le Q i s hs hslo hshi ζ m n⟩

end EinsteinFull
