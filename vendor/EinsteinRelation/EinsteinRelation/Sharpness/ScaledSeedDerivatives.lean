import EinsteinRelation.Sharpness.SeedFieldDerivatives
import EinsteinRelation.Sharpness.SeedCommonJetBound
import Mathlib.Analysis.Calculus.FDeriv.Mul
open MeasureTheory
namespace EinsteinRelation.Sharpness
/-- Actual iterated coordinate derivatives commute with constant multiplication.
Source main.tex1218, used for the second and third jets of ψ=εh. -/
theorem iteratedCoordinateDerivative_const_mul {d : ℕ} (f : Vec d → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (c : ℝ) (is : List (Fin d)) :
    iteratedCoordinateDerivative is (fun y => c * f y) =
      fun x => c * iteratedCoordinateDerivative is f x := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    rw [iteratedCoordinateDerivative_cons, ih]
    funext x
    change coordinateDerivative i (fun y => c * iteratedCoordinateDerivative is f y) x =
      c * coordinateDerivative i (iteratedCoordinateDerivative is f) x
    unfold coordinateDerivative
    have hd : DifferentiableAt ℝ (iteratedCoordinateDerivative is f) x :=
      (contDiff_iteratedCoordinateDerivative f hf is).differentiable (by simp) x
    rw [fderiv_const_mul hd c, ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- Actual scaled seed jets, with the same ε in every derivative. -/
theorem iteratedCoordinateDerivative_scaled_seedField {d : ℕ} (ε : ℝ)
    (W : NoiseSample d) (is : List (Fin d)) (x : Vec d) :
    iteratedCoordinateDerivative is (fun y => ε * seedField d W y) x =
      ε * iteratedCoordinateDerivative is (seedField d W) x :=
  congrFun (iteratedCoordinateDerivative_const_mul (seedField d W) (contDiff_seedField d W) ε is) x

/-- For each fixed scale, all scaled seed jets up to order three admit one deterministic bound
before every actual sample and point. No probability or extra regularity premise. -/
theorem exists_uniform_scaled_seedField_third_jet_bound (d : ℕ) (ε : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (W : NoiseSample d) (x : Vec d),
      |ε * seedField d W x| ≤ M ∧
      (∀ i : Fin d, |coordinateDerivative i (fun y => ε * seedField d W y) x| ≤ M) ∧
      (∀ i j : Fin d, |coordinateDerivative i
        (coordinateDerivative j (fun y => ε * seedField d W y)) x| ≤ M) ∧
      ∀ i j k : Fin d, |coordinateDerivative i (coordinateDerivative j
        (coordinateDerivative k (fun y => ε * seedField d W y))) x| ≤ M := by
  obtain ⟨M, hM, hbound⟩ := exists_uniform_seedField_third_jet_bound d
  refine ⟨|ε| * M, mul_nonneg (abs_nonneg ε) (by linarith), ?_⟩
  intro W x
  have hb := hbound W x
  have hscaled (is : List (Fin d)) :
      |iteratedCoordinateDerivative is (fun y => ε * seedField d W y) x| =
        |ε| * |iteratedCoordinateDerivative is (seedField d W) x| := by
    rw [iteratedCoordinateDerivative_scaled_seedField, abs_mul]
  refine ⟨?_, fun i => ?_, fun i j => ?_, fun i j k => ?_⟩
  · rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hb.1 (abs_nonneg ε)
  · change |iteratedCoordinateDerivative [i] (fun y => ε * seedField d W y) x| ≤ _
    rw [hscaled]
    exact mul_le_mul_of_nonneg_left (hb.2.1 i) (abs_nonneg ε)
  · change |iteratedCoordinateDerivative [i,j] (fun y => ε * seedField d W y) x| ≤ _
    rw [hscaled]
    exact mul_le_mul_of_nonneg_left (hb.2.2.1 i j) (abs_nonneg ε)
  · change |iteratedCoordinateDerivative [i,j,k] (fun y => ε * seedField d W y) x| ≤ _
    rw [hscaled]
    exact mul_le_mul_of_nonneg_left (hb.2.2.2 i j k) (abs_nonneg ε)
end EinsteinRelation.Sharpness
