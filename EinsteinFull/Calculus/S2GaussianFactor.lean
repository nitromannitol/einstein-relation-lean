import EinsteinFull.Work.W3.GaussianConvolutionSupport

/-!
# Isotropic deconvolution of an anisotropic Gaussian

For a positive definite `A'` and `ε > 0` the density with covariance `t (A' + ε I)` is the
convolution of the isotropic density with covariance `ε t I` and the density with covariance
`t A'`. The pointwise product identity is proved by completing the square, with an explicit
bridge covariance and bridge shift; no spectral decomposition is used.
-/

namespace EinsteinFull

open EinsteinRelation MeasureTheory

variable {d : ℕ}

/-- The sum matrix `A' + ε I`. -/
noncomputable def gaussSumMat (A' : Mat d) (ε : ℝ) : Mat d := A' + ε • (1 : Mat d)

/-- The bridge precision `ε⁻¹ I + A'⁻¹`. -/
noncomputable def bridgePrecision (A' : Mat d) (ε : ℝ) : Mat d := ε⁻¹ • (1 : Mat d) + A'⁻¹

/-- The bridge covariance is the inverse bridge precision. -/
noncomputable def bridgeCovariance (A' : Mat d) (ε : ℝ) : Mat d := (bridgePrecision A' ε)⁻¹

/-- The bridge mean is `A' (A' + ε I)⁻¹ x`. -/
noncomputable def bridgeShift (A' : Mat d) (ε : ℝ) : Mat d := A' * (gaussSumMat A' ε)⁻¹

theorem posDef_transpose_eq {M : Mat d} (h : M.PosDef) : M.transpose = M := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using h.isHermitian.eq

theorem posDef_one_smul {ε : ℝ} (hε : 0 < ε) : (ε • (1 : Mat d)).PosDef :=
  (show (1 : Mat d).PosDef from Matrix.PosDef.one).smul hε

theorem posDef_gaussSumMat {A' : Mat d} (hA' : A'.PosDef) {ε : ℝ} (hε : 0 < ε) :
    (gaussSumMat A' ε).PosDef :=
  hA'.add_posSemidef (posDef_one_smul hε).posSemidef

theorem posDef_bridgePrecision {A' : Mat d} (hA' : A'.PosDef) {ε : ℝ} (hε : 0 < ε) :
    (bridgePrecision A' ε).PosDef :=
  (posDef_one_smul (inv_pos.mpr hε)).add hA'.inv

theorem posDef_bridgeCovariance {A' : Mat d} (hA' : A'.PosDef) {ε : ℝ} (hε : 0 < ε) :
    (bridgeCovariance A' ε).PosDef :=
  (posDef_bridgePrecision hA' hε).inv

theorem isUnit_det_of_posDef {M : Mat d} (h : M.PosDef) : IsUnit M.det :=
  isUnit_iff_ne_zero.mpr h.det_pos.ne'

/-- Symmetric matrices move across a dot product. -/
theorem dotProduct_mulVec_symm {B : Mat d} (hB : B.transpose = B) (a c : Vec d) :
    dotProduct (B.mulVec a) c = dotProduct a (B.mulVec c) := by
  calc dotProduct (B.mulVec a) c = dotProduct (Matrix.vecMul a B.transpose) c := by
        rw [Matrix.vecMul_transpose]
    _ = dotProduct (Matrix.vecMul a B) c := by rw [hB]
    _ = dotProduct a (B.mulVec c) := (Matrix.dotProduct_mulVec a B c).symm

/-- The double-sum quadratic form is the dot-product quadratic form. -/
theorem quad_eq_dot (B : Mat d) (v : Vec d) :
    (∑ j, ∑ k, v j * B j k * v k) = dotProduct v (B.mulVec v) := by
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

theorem det_gaussSumMat {A' : Mat d} (hA' : A'.PosDef) {ε : ℝ} (hε : 0 < ε) :
    (gaussSumMat A' ε).det = ε ^ d * A'.det * (bridgePrecision A' ε).det := by
  have h1 : A' * A'⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_det_of_posDef hA')
  have hs : gaussSumMat A' ε = ε • (A' * bridgePrecision A' ε) := by
    unfold gaussSumMat bridgePrecision
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, h1, smul_add, smul_smul,
      mul_inv_cancel₀ hε.ne', one_smul]
  rw [hs, Matrix.det_smul, Matrix.det_mul, Fintype.card_fin]
  ring

theorem det_bridgeCovariance (A' : Mat d) (ε : ℝ) :
    (bridgeCovariance A' ε).det = (bridgePrecision A' ε).det⁻¹ := by
  unfold bridgeCovariance
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv]

/-- The completed-square identity in dot-product form. -/
theorem gaussian_quadratic_factor {A' : Mat d} (hA' : A'.PosDef) {ε : ℝ} (hε : 0 < ε)
    (x y : Vec d) :
    dotProduct (x - y) (x - y) / ε + dotProduct y (A'⁻¹.mulVec y) =
      dotProduct x ((gaussSumMat A' ε)⁻¹.mulVec x) +
        dotProduct (y - (bridgeShift A' ε).mulVec x)
          ((bridgePrecision A' ε).mulVec (y - (bridgeShift A' ε).mulVec x)) := by
  have hsA : A'.transpose = A' := posDef_transpose_eq hA'
  have hA'unit := isUnit_det_of_posDef hA'
  have hĀunit := isUnit_det_of_posDef (posDef_gaussSumMat hA' hε)
  obtain ⟨u, hu⟩ : ∃ u : Vec d, u = (gaussSumMat A' ε)⁻¹.mulVec x := ⟨_, rfl⟩
  have hxu : (gaussSumMat A' ε).mulVec u = x := by
    rw [hu, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hĀunit, Matrix.one_mulVec]
  have hĀu : (gaussSumMat A' ε).mulVec u = A'.mulVec u + ε • u := by
    unfold gaussSumMat
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hM : (bridgeShift A' ε).mulVec x = A'.mulVec u := by
    unfold bridgeShift
    rw [← Matrix.mulVec_mulVec, ← hu]
  obtain ⟨w, hw⟩ : ∃ w : Vec d, w = y - A'.mulVec u := ⟨_, rfl⟩
  have hy : y = A'.mulVec u + w := by rw [hw]; abel
  have hx : x = A'.mulVec u + ε • u := by rw [← hĀu, hxu]
  have hxy : x - y = ε • u - w := by rw [hx, hw]; abel
  have hε0 : ε ≠ 0 := hε.ne'
  have hA1 : A'⁻¹.mulVec y = u + A'⁻¹.mulVec w := by
    rw [hy, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hA'unit,
      Matrix.one_mulVec]
  have hAu : dotProduct (A'.mulVec u) (A'⁻¹.mulVec w) = dotProduct u w := by
    rw [dotProduct_mulVec_symm hsA, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hA'unit,
      Matrix.one_mulVec]
  have hcomm : dotProduct w u = dotProduct u w := dotProduct_comm _ _
  have hG : (bridgePrecision A' ε).mulVec w = ε⁻¹ • w + A'⁻¹.mulVec w := by
    unfold bridgePrecision
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [hM, ← hw, ← hu, hxy, hA1, hG]
  rw [show dotProduct y (u + A'⁻¹.mulVec w) =
      dotProduct (A'.mulVec u + w) (u + A'⁻¹.mulVec w) by rw [← hy]]
  rw [hx]
  simp only [sub_dotProduct, dotProduct_sub, add_dotProduct, dotProduct_add, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, hAu, hcomm]
  field_simp
  ring

/-- Prefactor identity for the isotropic deconvolution. -/
theorem gaussian_prefactor_factor {A' : Mat d} (hA' : A'.PosDef) {ε t : ℝ} (hε : 0 < ε)
    (ht : 0 < t) :
    (2 * Real.pi * (ε * t)) ^ (-(d : ℝ) / 2) / Real.sqrt (1 : Mat d).det *
        ((2 * Real.pi * t) ^ (-(d : ℝ) / 2) / Real.sqrt A'.det) =
      (2 * Real.pi * t) ^ (-(d : ℝ) / 2) / Real.sqrt (gaussSumMat A' ε).det *
        ((2 * Real.pi * t) ^ (-(d : ℝ) / 2) /
          Real.sqrt (bridgeCovariance A' ε).det) := by
  have hpi : 0 < 2 * Real.pi * t := mul_pos (mul_pos two_pos Real.pi_pos) ht
  have hdG := (posDef_bridgePrecision hA' hε).det_pos
  have hdA := hA'.det_pos
  have hdS := (posDef_gaussSumMat hA' hε).det_pos
  have hdsum := det_gaussSumMat hA' hε
  have hdB := det_bridgeCovariance A' ε
  have hq : Real.sqrt (gaussSumMat A' ε).det * Real.sqrt (bridgeCovariance A' ε).det =
      Real.sqrt (ε ^ d) * Real.sqrt A'.det := by
    rw [← Real.sqrt_mul hdS.le, ← Real.sqrt_mul (pow_nonneg hε.le d), hdB, hdsum]
    congr 1
    field_simp
  have hε' : ε ^ (-(d : ℝ) / 2) = (Real.sqrt (ε ^ d))⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (pow_nonneg hε.le d), ← Real.rpow_natCast,
      ← Real.rpow_mul hε.le]
    congr 1
    ring
  have hmul : (2 * Real.pi * (ε * t)) ^ (-(d : ℝ) / 2) =
      (2 * Real.pi * t) ^ (-(d : ℝ) / 2) * ε ^ (-(d : ℝ) / 2) := by
    rw [show 2 * Real.pi * (ε * t) = (2 * Real.pi * t) * ε by ring,
      Real.mul_rpow hpi.le hε.le]
  have hsε : 0 < Real.sqrt (ε ^ d) := Real.sqrt_pos.mpr (pow_pos hε d)
  have hsA : 0 < Real.sqrt A'.det := Real.sqrt_pos.mpr hdA
  have hsε' := hsε.ne'
  have hsA' := hsA.ne'
  rw [div_mul_div_comm ((2 * Real.pi * t) ^ (-(d : ℝ) / 2))
    (Real.sqrt (gaussSumMat A' ε).det) ((2 * Real.pi * t) ^ (-(d : ℝ) / 2))
    (Real.sqrt (bridgeCovariance A' ε).det), hq, hmul, hε', Matrix.det_one, Real.sqrt_one]
  field_simp

theorem exp_arith_aux (ε t Q1 Q2 R1 R2 : ℝ) (h : Q1 / ε + Q2 = R1 + R2) :
    -Q1 / (2 * (ε * t)) + -Q2 / (2 * t) = -R1 / (2 * t) + -R2 / (2 * t) := by
  have e1 : -Q1 / (2 * (ε * t)) + -Q2 / (2 * t) = -(Q1 / ε + Q2) / (2 * t) := by ring
  have e2 : -R1 / (2 * t) + -R2 / (2 * t) = -(R1 + R2) / (2 * t) := by ring
  rw [e1, e2, h]

/-- The pointwise product identity: isotropic times `A'` is sum times bridge. -/
theorem anisotropicGaussian_factor {A' : Mat d} (hA' : A'.PosDef) {ε t : ℝ} (hε : 0 < ε)
    (ht : 0 < t) (x y : Vec d) :
    anisotropicGaussian (1 : Mat d) (ε * t) (x - y) * anisotropicGaussian A' t y =
      anisotropicGaussian (gaussSumMat A' ε) t x *
        anisotropicGaussian (bridgeCovariance A' ε) t
          (y - (bridgeShift A' ε).mulVec x) := by
  have hGunit := isUnit_det_of_posDef (posDef_bridgePrecision hA' hε)
  have hinv : (bridgeCovariance A' ε)⁻¹ = bridgePrecision A' ε :=
    Matrix.nonsing_inv_nonsing_inv _ hGunit
  have hq := gaussian_quadratic_factor hA' hε x y
  have hpre := gaussian_prefactor_factor hA' hε ht
  unfold anisotropicGaussian
  rw [hinv]
  simp only [quad_eq_dot, inv_one, Matrix.one_mulVec]
  have hexp := exp_arith_aux ε t (dotProduct (x - y) (x - y)) (dotProduct y (A'⁻¹.mulVec y))
    (dotProduct x ((gaussSumMat A' ε)⁻¹.mulVec x))
    (dotProduct (y - (bridgeShift A' ε).mulVec x)
      ((bridgePrecision A' ε).mulVec (y - (bridgeShift A' ε).mulVec x))) hq
  calc _ = ((2 * Real.pi * (ε * t)) ^ (-(d : ℝ) / 2) / Real.sqrt (1 : Mat d).det *
          ((2 * Real.pi * t) ^ (-(d : ℝ) / 2) / Real.sqrt A'.det)) *
        Real.exp (-dotProduct (x - y) (x - y) / (2 * (ε * t)) +
          -dotProduct y (A'⁻¹.mulVec y) / (2 * t)) := by
        rw [Real.exp_add]; ring
    _ = _ := by
        rw [hpre, hexp, Real.exp_add]; ring

end EinsteinFull
