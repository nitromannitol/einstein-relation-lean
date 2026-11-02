import EinsteinFull.Calculus.S2GaussianFactor

/-!
# Moments of the isotropic deconvolution

Integrals of the pointwise factorization `anisotropicGaussian_factor`: the plain convolution,
the convolution twisted by the linear weight `A'⁻¹ y`, and an `L¹` bound of that weight against
the `A'` density.
-/

namespace EinsteinFull

open EinsteinRelation MeasureTheory

variable {d : ℕ}

theorem anisotropicGaussian_nonneg (A : Mat d) {s : ℝ} (hs : 0 < s) (y : Vec d) :
    0 ≤ anisotropicGaussian A s y := by
  unfold anisotropicGaussian
  positivity

theorem integral_isotropic_mul_gaussian {A' : Mat d} (hA' : A'.PosDef) {ε t : ℝ}
    (hε : 0 < ε) (ht : 0 < t) (x : Vec d) :
    (∫ y : Vec d, anisotropicGaussian (1 : Mat d) (ε * t) (x - y) *
        anisotropicGaussian A' t y) =
      anisotropicGaussian (gaussSumMat A' ε) t x := by
  simp_rw [anisotropicGaussian_factor hA' hε ht x]
  rw [integral_const_mul, integral_sub_right_eq_self
    (anisotropicGaussian (bridgeCovariance A' ε) t) ((bridgeShift A' ε).mulVec x),
    integral_anisotropicGaussian _ (posDef_bridgeCovariance hA' hε) t ht, mul_one]

theorem integral_linear_isotropic_mul_gaussian {A' : Mat d} (hA' : A'.PosDef) {ε t : ℝ}
    (hε : 0 < ε) (ht : 0 < t) (j : Fin d) (x : Vec d) :
    (∫ y : Vec d, (A'⁻¹.mulVec y) j *
        (anisotropicGaussian (1 : Mat d) (ε * t) (x - y) * anisotropicGaussian A' t y)) =
      ((gaussSumMat A' ε)⁻¹.mulVec x) j * anisotropicGaussian (gaussSumMat A' ε) t x := by
  have hB := posDef_bridgeCovariance hA' hε
  have hA'unit := isUnit_det_of_posDef hA'
  simp_rw [anisotropicGaussian_factor hA' hε ht x]
  have h1 : (fun y : Vec d => (A'⁻¹.mulVec y) j *
      (anisotropicGaussian (gaussSumMat A' ε) t x *
        anisotropicGaussian (bridgeCovariance A' ε) t (y - (bridgeShift A' ε).mulVec x))) =
      fun y => anisotropicGaussian (gaussSumMat A' ε) t x *
        ((A'⁻¹.mulVec y) j * anisotropicGaussian (bridgeCovariance A' ε) t
          (y - (bridgeShift A' ε).mulVec x)) := by
    funext y
    ring
  rw [h1, integral_const_mul]
  have h2 := integral_add_right_eq_self (μ := (volume : Measure (Vec d)))
    (fun y : Vec d => (A'⁻¹.mulVec y) j *
      anisotropicGaussian (bridgeCovariance A' ε) t (y - (bridgeShift A' ε).mulVec x))
    ((bridgeShift A' ε).mulVec x)
  rw [← h2]
  simp only [add_sub_cancel_right]
  have h3 : ∀ y : Vec d, (A'⁻¹.mulVec (y + (bridgeShift A' ε).mulVec x)) j *
      anisotropicGaussian (bridgeCovariance A' ε) t y =
      (A'⁻¹.mulVec y) j * anisotropicGaussian (bridgeCovariance A' ε) t y +
        (A'⁻¹.mulVec ((bridgeShift A' ε).mulVec x)) j *
          anisotropicGaussian (bridgeCovariance A' ε) t y := by
    intro y
    rw [Matrix.mulVec_add]
    simp only [Pi.add_apply]
    ring
  simp_rw [h3]
  rw [integral_add (integrable_mulVec_mul_anisotropicGaussian _ hB A'⁻¹ j t ht)
    ((integrable_anisotropicGaussian _ hB t ht).const_mul _),
    integral_mulVec_mul_anisotropicGaussian, integral_const_mul,
    integral_anisotropicGaussian _ hB t ht]
  have hm : A'⁻¹.mulVec ((bridgeShift A' ε).mulVec x) = (gaussSumMat A' ε)⁻¹.mulVec x := by
    unfold bridgeShift
    rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hA'unit,
      Matrix.one_mul]
  rw [hm]
  ring

/-- `L¹` bound of the linear weight `A⁻¹ y` against the centered density of covariance `s A`. -/
theorem integral_abs_linear_gaussian_le {A : Mat d} (hA : A.PosDef) (j : Fin d) {s c : ℝ}
    (hs : 0 < s) (hc : 0 < c) :
    (∫ y : Vec d, |(A⁻¹.mulVec y) j| * anisotropicGaussian A s y) ≤
      (s * (A⁻¹) j j / c + c) / 2 := by
  have hi2 := integrable_mulVec_mulVec_mul_anisotropicGaussian A hA A⁻¹ A⁻¹ j j s hs
  have hi0 := integrable_anisotropicGaussian A hA s hs
  have hiabs : Integrable (fun y : Vec d => |(A⁻¹.mulVec y) j| * anisotropicGaussian A s y) := by
    refine ((integrable_mulVec_mul_anisotropicGaussian A hA A⁻¹ j s hs).abs).congr ?_
    exact Filter.Eventually.of_forall fun y => by
      simp only [abs_mul, abs_of_nonneg (anisotropicGaussian_nonneg A hs y)]
  have hibound : Integrable (fun y : Vec d => 1 / (2 * c) *
      ((A⁻¹.mulVec y) j * (A⁻¹.mulVec y) j * anisotropicGaussian A s y) +
        c / 2 * anisotropicGaussian A s y) :=
    (hi2.const_mul _).add (hi0.const_mul _)
  have hbound : ∀ y : Vec d, |(A⁻¹.mulVec y) j| * anisotropicGaussian A s y ≤
      1 / (2 * c) * ((A⁻¹.mulVec y) j * (A⁻¹.mulVec y) j * anisotropicGaussian A s y) +
        c / 2 * anisotropicGaussian A s y := by
    intro y
    have hg := anisotropicGaussian_nonneg A hs y
    have ha2 : (A⁻¹.mulVec y) j * (A⁻¹.mulVec y) j = |(A⁻¹.mulVec y) j| * |(A⁻¹.mulVec y) j| :=
      (abs_mul_abs_self _).symm
    have key : 1 / (2 * c) * (|(A⁻¹.mulVec y) j| * |(A⁻¹.mulVec y) j|) + c / 2 -
        |(A⁻¹.mulVec y) j| = (|(A⁻¹.mulVec y) j| - c) ^ 2 / (2 * c) := by
      field_simp
      ring
    have hab : |(A⁻¹.mulVec y) j| ≤
        1 / (2 * c) * (|(A⁻¹.mulVec y) j| * |(A⁻¹.mulVec y) j|) + c / 2 := by
      have : 0 ≤ (|(A⁻¹.mulVec y) j| - c) ^ 2 / (2 * c) := by positivity
      linarith
    calc |(A⁻¹.mulVec y) j| * anisotropicGaussian A s y
        ≤ (1 / (2 * c) * (|(A⁻¹.mulVec y) j| * |(A⁻¹.mulVec y) j|) + c / 2) *
            anisotropicGaussian A s y := mul_le_mul_of_nonneg_right hab hg
      _ = _ := by rw [ha2]; ring
  calc (∫ y : Vec d, |(A⁻¹.mulVec y) j| * anisotropicGaussian A s y)
      ≤ ∫ y : Vec d, (1 / (2 * c) *
          ((A⁻¹.mulVec y) j * (A⁻¹.mulVec y) j * anisotropicGaussian A s y) +
            c / 2 * anisotropicGaussian A s y) := integral_mono hiabs hibound hbound
    _ = (s * (A⁻¹) j j / c + c) / 2 := by
        rw [integral_add (hi2.const_mul _) (hi0.const_mul _), integral_const_mul,
          integral_const_mul, integral_inv_mulVec_mulVec_mul_anisotropicGaussian A hA j j s hs,
          integral_anisotropicGaussian A hA s hs]
        field_simp

end EinsteinFull
