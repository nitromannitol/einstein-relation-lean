import EinsteinRelation.Sharpness.Fields
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Convolution

/-! Actual iterated coordinate derivatives for the deterministic bounds in
paper/main.tex1212–1216. No norm or probability-law convention is introduced. -/
namespace EinsteinRelation.Sharpness

/-- Ordered iteration of actual spatial coordinate derivatives. -/
noncomputable def iteratedCoordinateDerivative {d : ℕ} :
    List (Fin d) → (Vec d → ℝ) → Vec d → ℝ
  | [], f => f
  | i :: is, f => coordinateDerivative i (iteratedCoordinateDerivative is f)

@[simp] theorem iteratedCoordinateDerivative_nil {d : ℕ} (f : Vec d → ℝ) :
    iteratedCoordinateDerivative [] f = f := rfl

@[simp] theorem iteratedCoordinateDerivative_cons {d : ℕ} (i : Fin d)
    (is : List (Fin d)) (f : Vec d → ℝ) :
    iteratedCoordinateDerivative (i::is) f =
      coordinateDerivative i (iteratedCoordinateDerivative is f) := rfl

theorem contDiff_iteratedCoordinateDerivative {d : ℕ} (f : Vec d → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (is : List (Fin d)) :
    ContDiff ℝ (⊤ : ℕ∞) (iteratedCoordinateDerivative is f) := by
  induction is with
  | nil => exact hf
  | cons i is ih =>
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun x => fderiv ℝ (iteratedCoordinateDerivative is f) x (unitVector i))
    exact (ih.fderiv_right (le_of_eq ENat.coe_top_add_one)).clm_apply contDiff_const

theorem hasCompactSupport_iteratedCoordinateDerivative {d : ℕ} (f : Vec d → ℝ)
    (hf : HasCompactSupport f) (is : List (Fin d)) :
    HasCompactSupport (iteratedCoordinateDerivative is f) := by
  induction is with
  | nil => exact hf
  | cons i is ih => exact ih.fderiv_apply ℝ (unitVector i)
end EinsteinRelation.Sharpness