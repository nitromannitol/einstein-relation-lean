import EinsteinRelation.Correctors.LinearKernelCalculus

/-! # Scalar factors in spatial kernel derivatives

Source: `paper/main.tex:1015–1018`. Exact derivative normalization for
the determinant factor in the homogenized coordinate change.
-/

noncomputable section
namespace EinsteinRelation.Correctors.KernelCalculus

/-- Derivative bounds for a fixed smooth kernel family after a linear change
(`paper/main.tex:1015–1018`). -/
theorem coordinateIterate_const_mul {d : ℕ} {K : Vec d → ℝ}
    (hK : ContDiff ℝ (⊤ : ℕ∞) K) (cs : List (Fin d)) (c : ℝ) :
    coordinateIterate cs (fun x => c * K x) = fun x => c * coordinateIterate cs K x := by
  induction cs with
  | nil => rfl
  | cons i rest ih =>
    have h_rest_smooth : ContDiff ℝ 1 (coordinateIterate rest K) :=
      (contDiff_coordinateIterate hK rest).of_le (by norm_cast)
    unfold coordinateIterate
    rw [ih]
    funext x
    unfold coordinateDerivative
    rw [fderiv_const_mul (h_rest_smooth.differentiable le_rfl x) c]
    simp

end EinsteinRelation.Correctors.KernelCalculus
