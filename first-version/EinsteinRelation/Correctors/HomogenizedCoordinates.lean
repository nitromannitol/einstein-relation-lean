import EinsteinRelation.Correctors.EllipticCoordinates
import EinsteinRelation.Correctors.HomogenizedMatrixBounds

/-! # Quantitative coordinates of the actual homogenized matrix

Source: `paper/main.tex:1003–1018`. The coordinate and inverse-coordinate
bounds depend only on the original ellipticity parameter.
-/

noncomputable section
namespace EinsteinRelation.Correctors

/-- Whitening coordinates for the actual homogenized matrix, with both
operator and entry bounds (`paper/main.tex:1003–1018`). -/
theorem exists_homogenized_coordinates {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) :
    ∃ T : Vec d ≃L[ℝ] Vec d,
      (let M : Mat d := fun i j => T (unitVector j) i;
        M * homogenizedMatrix Q * M.transpose = 1) ∧
      (∀ x, euclideanNorm (T x) ≤ Real.sqrt (sourceReducedBound Λ₀) * euclideanNorm x) ∧
      (∀ x, euclideanNorm (T.symm x) ≤ Real.sqrt (sourceReducedBound Λ₀) * euclideanNorm x) ∧
      (∀ i j : Fin d, |T (unitVector i) j| ≤ Real.sqrt (sourceReducedBound Λ₀)) := by
  have hΛ : 0 < Λ₀ := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
  have hpos : 0 < sourceReducedBound Λ₀ := by unfold sourceReducedBound; positivity
  obtain ⟨T, hT, hTb, hTi⟩ := exists_elliptic_coordinates hpos
    (homogenizedMatrix Q) (homogenizedMatrix_transpose Q)
    (homogenizedMatrix_quadratic_lower Q) (homogenizedMatrix_quadratic_upper Q)
  refine ⟨T, hT, hTb, hTi, fun i j => ?_⟩
  have hu : euclideanNorm (unitVector i : Vec d) = 1 := by
    simp [euclideanNorm, euclideanSq, dot, unitVector, Pi.single_apply]
  exact (abs_coord_le_euclideanNorm _ j).trans (by simpa only [hu, mul_one] using hTb (unitVector i))

/-- Each entry inherits the uniform column bound
(`paper/main.tex:1061–1082`). -/
theorem abs_homogenizedMatrix_entry_le {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i j : Fin d) :
    |homogenizedMatrix Q i j| ≤ sourceReducedBound Λ₀ := by
  have h := (abs_coord_le_euclideanNorm ((homogenizedMatrix Q).mulVec (unitVector j)) i).trans
    (homogenizedMatrix_euclideanNorm_mulVec_unitVector_le Q j)
  simpa [Matrix.mulVec, dotProduct, unitVector, Pi.single_apply] using h

end EinsteinRelation.Correctors
