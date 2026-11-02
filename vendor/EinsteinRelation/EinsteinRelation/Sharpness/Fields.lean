import EinsteinRelation.Sharpness.MatrixDefs
import EinsteinRelation.Calculus.Generator
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # The fields in the sharpness example

Literal formulas from `paper/main.tex`, `eq.sharp-coefficients`, lines 1218–1231.
The coefficient is evaluated on the actual spatial gradient of a scalar function.
Smoothness, stationarity, finite range, and nondegeneracy of a random choice of
that function remain separate proof obligations.
-/

namespace EinsteinRelation.Sharpness

/-- Reduced coefficient of the explicit deformation. -/
noncomputable def coefficientField {d : ℕ} (i : Fin d) (ψ : Vec d → ℝ)
    (x : Vec d) : Mat d := coefficient i (gradient ψ x)

/-- Clock density, defined by the divergence of the first coefficient column. -/
noncomputable def densityField {d : ℕ} (i : Fin d) (δ : ℝ) (ψ : Vec d → ℝ)
    (x : Vec d) : ℝ :=
  1 + δ / 2 * divergence (fun y => (coefficientField i ψ y).mulVec (unitVector i)) x

/-- The physical coefficient before moving the potential into the clock. -/
noncomputable def physicalCoefficientField {d : ℕ} (i : Fin d) (δ : ℝ)
    (ψ : Vec d → ℝ) (x : Vec d) : Mat d :=
  (densityField i δ ψ x)⁻¹ • coefficientField i ψ x

/-- The physical potential, on the region where the clock density is positive. -/
noncomputable def potentialField {d : ℕ} (i : Fin d) (δ : ℝ)
    (ψ : Vec d → ℝ) (x : Vec d) : ℝ :=
  -(1 / 2 : ℝ) * Real.log (densityField i δ ψ x)

/-- The literal potential recovers the constructed clock density. -/
theorem exp_neg_two_potentialField {d : ℕ} (i : Fin d) (δ : ℝ)
    (ψ : Vec d → ℝ) (x : Vec d) (hμ : 0 < densityField i δ ψ x) :
    Real.exp (-2 * potentialField i δ ψ x) = densityField i δ ψ x := by
  calc
    _ = Real.exp (Real.log (densityField i δ ψ x)) := by
      congr 1
      unfold potentialField
      ring
    _ = _ := Real.exp_log hμ

/-- Moving the potential into the coefficient recovers the explicit deformation. -/
theorem reduce_physicalCoefficientField {d : ℕ} (i : Fin d) (δ : ℝ)
    (ψ : Vec d → ℝ) (x : Vec d) (hμ : 0 < densityField i δ ψ x) :
    Real.exp (-2 * potentialField i δ ψ x) • physicalCoefficientField i δ ψ x =
      coefficientField i ψ x := by
  rw [exp_neg_two_potentialField i δ ψ x hμ, physicalCoefficientField,
    smul_smul, mul_inv_cancel₀ (ne_of_gt hμ), one_smul]

end EinsteinRelation.Sharpness
