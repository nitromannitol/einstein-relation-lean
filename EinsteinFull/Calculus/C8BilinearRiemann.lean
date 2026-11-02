import EinsteinFull.Calculus.C10TestBlocksSupport

/-! A uniform bilinear Riemann estimate for the literal covariance lattice. -/

noncomputable section

open EinsteinFull EinsteinRelation EinsteinRelation.External.AKM MeasureTheory ProbabilityTheory
open EinsteinRelation.Environment.AKMTestIntegralSupport

namespace EinsteinFull.Blueprint

/-- The full bilinear lattice sum approximates its spatial integral uniformly
over real matrices and meshes, with the original order of the Schwartz norms. -/
theorem bilinear_matrix_riemann_error (d N : ℕ) (hN : 2*d+10 < N) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℝ, 0 < a → a ≤ 1 →
    ∀ (M : Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ)
      (F G : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))),
    ‖(((a^d : ℝ) : ℂ) * ∑' j : Fin d → ℤ, ∑ u, ∑ v,
        F (covarianceTileCenter a j) u * (M u v : ℂ) * G (covarianceTileCenter a j) v) -
      ∫ x : Vec d, ∑ u, ∑ v, F x u * (M u v : ℂ) * G x v‖ ≤
      C * covarianceMatrixSize M * schwartzTestNorm N F * schwartzTestNorm N G * a := by
  let D : ℝ := (Fintype.card (JointObservationIndex d) : ℝ) ^ 2 *
    (d : ℝ) * (2 + (d : ℝ)) ^ (2 * N) * 3 ^ d
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨D + 1, by positivity, ?_⟩
  intro a ha ha1 M F G
  have h := EinsteinFull.Calculus.C10TestBlocks.bilinear_matrix_riemann_error_le
    (by omega : 1 ≤ N) (by omega : d ≤ N) ha ha1 M F G
  rw [norm_sub_rev] at h
  have hsize : 0 ≤ covarianceMatrixSize M := by unfold covarianceMatrixSize; positivity
  have hF := EinsteinFull.Calculus.C10TestBlocks.schwartz_norm_nonneg N F
  have hG := EinsteinFull.Calculus.C10TestBlocks.schwartz_norm_nonneg N G
  calc
    _ ≤ D * covarianceMatrixSize M * schwartzTestNorm N F * schwartzTestNorm N G * a := by
      convert h using 1
      dsimp only [D]
      ring
    _ ≤ _ := by gcongr; linarith

end EinsteinFull.Blueprint
