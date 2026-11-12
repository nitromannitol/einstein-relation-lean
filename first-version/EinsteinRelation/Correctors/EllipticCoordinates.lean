import EinsteinRelation.Correctors.EllipticSquareRoot
import EinsteinRelation.Correctors.LinearKernelCalculus

/-! # Elliptic coordinates for the anisotropic kernel construction

Source: `paper/main.tex:1003–1018`. The inverse symmetric square root
whitens the coefficient matrix and controls both coordinate maps in the
Euclidean norm.
-/

noncomputable section
namespace EinsteinRelation.Correctors

/-- Actual inverse square-root coordinates with whitening and Euclidean
bounds (`paper/main.tex:1003–1018`). -/
theorem exists_elliptic_coordinates {d : ℕ} {L : ℝ} (hL : 0 < L) (A : Mat d)
    (hA : A.transpose = A)
    (hlow : ∀ x : Vec d, L⁻¹ * euclideanSq x ≤ dot x (A.mulVec x))
    (hup : ∀ x : Vec d, dot x (A.mulVec x) ≤ L * euclideanSq x) :
    ∃ B : Vec d ≃L[ℝ] Vec d,
      (let M : Mat d := fun i j => (B (unitVector j)) i
       M * A * M.transpose = 1) ∧
      (∀ x, euclideanNorm (B x) ≤ Real.sqrt L * euclideanNorm x) ∧
      (∀ x, euclideanNorm (B.symm x) ≤ Real.sqrt L * euclideanNorm x) := by
  rcases exists_elliptic_squareRoot hL A hA hlow hup with
    ⟨S, hSsym, hSsq, hSi, hSb, hSib⟩
  have hSdet : IsUnit (Matrix.det S) :=
    (Matrix.isUnit_iff_isUnit_det S).mp hSi
  have hSinv_symm : S⁻¹.transpose = S⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hSsym]
  have hSinv_unit : IsUnit (S⁻¹ : Mat d) := by
    simpa [Units.val_inv] using hSi.unit⁻¹.isUnit
  have hSinv_inv : Invertible (S⁻¹ : Mat d) :=
    hSinv_unit.invertible
  let B_lin : (Fin d → ℝ) ≃ₗ[ℝ] (Fin d → ℝ) :=
    Matrix.toLinearEquiv' (S⁻¹) hSinv_inv
  have hB_lin_apply (x : Fin d → ℝ) : B_lin x = S⁻¹.mulVec x :=
    rfl
  have h_invOf : ⅟(S⁻¹ : Mat d) = S :=
    invOf_eq_left_inv (Matrix.mul_nonsing_inv (A := S) hSdet)
  have hB_lin_symm_apply (x : Fin d → ℝ) : B_lin.symm x = S.mulVec x := by
    calc
      B_lin.symm x = (Matrix.toLin' (⅟(S⁻¹ : Mat d))) x := rfl
      _ = (Matrix.toLin' S) x := by rw [h_invOf]
      _ = S.mulVec x := by rw [Matrix.toLin'_apply]
  let B : Vec d ≃L[ℝ] Vec d :=
    LinearEquiv.toContinuousLinearEquiv B_lin
  have hB_apply (x : Vec d) : B x = S⁻¹.mulVec x := by
    simpa [LinearEquiv.coe_toContinuousLinearEquiv'] using hB_lin_apply x
  have hBsymm_apply (x : Vec d) : B.symm x = S.mulVec x := by
    simpa [LinearEquiv.coe_toContinuousLinearEquiv_symm'] using hB_lin_symm_apply x
  have hM_eq_Sinv : (fun i j => (B (unitVector j)) i) = S⁻¹ := by
    ext i j
    simp [hB_apply, Matrix.mulVec, dotProduct, unitVector]
    rw [← dotProduct]
    rw [dotProduct_single]
    simp
  refine ⟨B, ?_, ?_, ?_⟩
  · intro M
    have hM : M = S⁻¹ := hM_eq_Sinv
    rw [hM]
    rw [hSinv_symm]
    rw [← hSsq]
    calc
      S⁻¹ * (S * S) * S⁻¹ = (S⁻¹ * S) * (S * S⁻¹) := by
        simp [Matrix.mul_assoc]
      _ = 1 * 1 := by rw [Matrix.nonsing_inv_mul (A := S) hSdet, Matrix.mul_nonsing_inv (A := S) hSdet]
      _ = 1 := by simp
  · intro x
    rw [hB_apply x]
    exact hSib x
  · intro x
    rw [hBsymm_apply x]
    exact hSb x

end EinsteinRelation.Correctors
