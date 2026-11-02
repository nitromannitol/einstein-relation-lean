import EinsteinFull.Calculus.S2GaussianDeconvMoments
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# The deconvolution matrix of the homogenized coefficient

With `K = sourceReducedBound Λ₀` and `ε = (2K)⁻¹`, the matrix `A' = ā - ε I` is positive
definite, `A' + ε I = ā`, and the diagonal of `A'⁻¹` is at most `2K`.
-/

namespace EinsteinFull

open EinsteinRelation MeasureTheory

variable {d : ℕ} {Λ₀ r₀ : ℝ}

theorem sourceReducedBound_pos_of_law (Q : EnvironmentLaw d Λ₀ r₀) :
    0 < sourceReducedBound Λ₀ := by
  unfold sourceReducedBound
  exact mul_pos (Real.exp_pos _) (by nlinarith [Q.ellipticity_parameter, sq_nonneg Λ₀])

/-- The isotropic fraction `(2K)⁻¹` removed from the coefficient. -/
noncomputable def deconvEps (Λ₀ : ℝ) : ℝ := (2 * sourceReducedBound Λ₀)⁻¹

/-- The remainder `ā - ε I`. -/
noncomputable def deconvMat (Q : EnvironmentLaw d Λ₀ r₀) : Mat d :=
  homogenizedCoefficient Q - deconvEps Λ₀ • (1 : Mat d)

theorem deconvEps_pos (Q : EnvironmentLaw d Λ₀ r₀) : 0 < deconvEps Λ₀ :=
  inv_pos.mpr (mul_pos two_pos (sourceReducedBound_pos_of_law Q))

theorem gaussSumMat_deconvMat (Q : EnvironmentLaw d Λ₀ r₀) :
    gaussSumMat (deconvMat Q) (deconvEps Λ₀) = homogenizedCoefficient Q := by
  unfold gaussSumMat deconvMat
  exact sub_add_cancel _ _

theorem coefficient_quadratic_lower (Q : EnvironmentLaw d Λ₀ r₀) (x : Vec d) :
    (sourceReducedBound Λ₀)⁻¹ * dotProduct x x ≤
      dotProduct x ((homogenizedCoefficient Q).mulVec x) :=
  ((homogenizedMatrix_isElliptic Q (0 : Vec d)).2 x).1

theorem deconvMat_quadratic_lower (Q : EnvironmentLaw d Λ₀ r₀) (x : Vec d) :
    deconvEps Λ₀ * dotProduct x x ≤ dotProduct x ((deconvMat Q).mulVec x) := by
  have h := coefficient_quadratic_lower Q x
  have hK := sourceReducedBound_pos_of_law Q
  have e : 2 * deconvEps Λ₀ = (sourceReducedBound Λ₀)⁻¹ := by
    unfold deconvEps
    field_simp
  rw [← e] at h
  unfold deconvMat
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
    dotProduct_smul, smul_eq_mul]
  linarith

theorem posDef_deconvMat (Q : EnvironmentLaw d Λ₀ r₀) : (deconvMat Q).PosDef := by
  have hε := deconvEps_pos Q
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, ?_⟩
  · have h1 : (homogenizedCoefficient Q).IsHermitian := by
      unfold Matrix.IsHermitian
      rw [Matrix.conjTranspose_eq_transpose_of_trivial]
      exact homogenizedMatrix_transpose Q
    exact h1.sub (posDef_one_smul hε).isHermitian
  · intro x hx
    have hs : star x = x := by
      ext i
      simp
    rw [hs]
    have hpos : 0 < dotProduct x x := by
      refine lt_of_le_of_ne ?_ (fun h => hx (dotProduct_self_eq_zero.mp h.symm))
      simp only [dotProduct]
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    have := deconvMat_quadratic_lower Q x
    nlinarith [mul_pos hε hpos]

theorem deconvMat_inv_diag_le (Q : EnvironmentLaw d Λ₀ r₀) (j : Fin d) :
    ((deconvMat Q)⁻¹) j j ≤ 2 * sourceReducedBound Λ₀ := by
  have hA := posDef_deconvMat Q
  have hunit := isUnit_det_of_posDef hA
  have hK := sourceReducedBound_pos_of_law Q
  have hε := deconvEps_pos Q
  obtain ⟨v, hv⟩ : ∃ v : Vec d, v = (deconvMat Q)⁻¹.mulVec (Pi.single j (1 : ℝ)) := ⟨_, rfl⟩
  have hAv : (deconvMat Q).mulVec v = Pi.single j (1 : ℝ) := by
    rw [hv, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]
  have hvj : v j = (deconvMat Q)⁻¹ j j := by
    rw [hv, Matrix.mulVec_single_one]
    first | rfl | simp [Matrix.col]
  have hq : dotProduct v ((deconvMat Q).mulVec v) = v j := by
    rw [hAv, dotProduct_single, mul_one]
  have hlow := deconvMat_quadratic_lower Q v
  rw [hq] at hlow
  have hsq : v j * v j ≤ dotProduct v v := by
    simp only [dotProduct]
    exact Finset.single_le_sum (f := fun i => v i * v i) (fun i _ => mul_self_nonneg (v i))
      (Finset.mem_univ j)
  have hvv : 0 ≤ dotProduct v v := by
    simp only [dotProduct]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hε1 : deconvEps Λ₀ * (2 * sourceReducedBound Λ₀) = 1 := by
    unfold deconvEps
    field_simp
  rw [← hvj]
  by_contra hcon
  push_neg at hcon
  have hq0 : 0 < v j := lt_trans (by positivity) hcon
  have h1 : deconvEps Λ₀ * v j * (2 * sourceReducedBound Λ₀) = v j := by
    calc deconvEps Λ₀ * v j * (2 * sourceReducedBound Λ₀)
        = v j * (deconvEps Λ₀ * (2 * sourceReducedBound Λ₀)) := by ring
      _ = v j := by rw [hε1, mul_one]
  have h2 : deconvEps Λ₀ * (v j * v j) ≤ v j :=
    (mul_le_mul_of_nonneg_left hsq hε.le).trans hlow
  nlinarith [mul_pos (mul_pos hε hq0) (sub_pos.mpr hcon)]

/-- `L¹` bound of the linear weight against the `A'` density. -/
theorem deconv_linear_L1_le (Q : EnvironmentLaw d Λ₀ r₀) (j : Fin d) {u : ℝ} (hu : 0 < u) :
    (∫ y : Vec d, |((deconvMat Q)⁻¹.mulVec y) j| * anisotropicGaussian (deconvMat Q) u y) ≤
      Real.sqrt (2 * sourceReducedBound Λ₀ * u) := by
  have hK := sourceReducedBound_pos_of_law Q
  have hc : 0 < Real.sqrt (2 * sourceReducedBound Λ₀ * u) :=
    Real.sqrt_pos.mpr (by positivity)
  have hcc : Real.sqrt (2 * sourceReducedBound Λ₀ * u) * Real.sqrt (2 * sourceReducedBound Λ₀ * u) =
      2 * sourceReducedBound Λ₀ * u := Real.mul_self_sqrt (by positivity)
  have h := integral_abs_linear_gaussian_le (posDef_deconvMat Q) j hu hc
  have hq := deconvMat_inv_diag_le Q j
  have h3 : u * ((deconvMat Q)⁻¹) j j / Real.sqrt (2 * sourceReducedBound Λ₀ * u) ≤
      Real.sqrt (2 * sourceReducedBound Λ₀ * u) := by
    rw [div_le_iff₀ hc]
    calc u * ((deconvMat Q)⁻¹) j j ≤ u * (2 * sourceReducedBound Λ₀) :=
        mul_le_mul_of_nonneg_left hq hu.le
      _ = _ := by rw [mul_comm u, hcc]
  linarith

end EinsteinFull
