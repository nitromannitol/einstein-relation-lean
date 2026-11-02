import EinsteinRelation.Calculus.HorizontalCore
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.Algebra.Support

/-! # Derivative scaling for compact kernels

Source: `paper/main.tex:1000–1008`, the bounds for every derivative of the
dyadic Poisson kernels in Proposition 6.1. Coordinate derivatives are literal
Fréchet derivatives on the existing carrier `Vec d`.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors.KernelCalculus

variable {d : ℕ}

/-- Every iterated coordinate derivative of a smooth kernel is smooth
(`paper/main.tex:1005–1008`). -/
theorem contDiff_coordinateIterate {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (cs : List (Fin d)) :
    ContDiff ℝ (⊤ : ℕ∞) (coordinateIterate cs f) := by
  induction cs with
  | nil => exact hf
  | cons i rest ih =>
    exact ((contDiff_infty_iff_fderiv.mp ih).2).clm_apply contDiff_const

/-- Coordinate derivatives preserve compact support
(`paper/main.tex:1005–1008`). -/
theorem hasCompactSupport_coordinateIterate {f : Vec d → ℝ}
    (hf : HasCompactSupport f) (cs : List (Fin d)) :
    HasCompactSupport (coordinateIterate cs f) := by
  induction cs with
  | nil => exact hf
  | cons i rest ih => exact ih.fderiv_apply ℝ (unitVector i)

/-- All coordinate derivatives of a smooth compact kernel are integrable
(`paper/main.tex:1005–1008`). -/
theorem integrable_coordinateIterate {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) (cs : List (Fin d)) :
    Integrable (coordinateIterate cs f) volume :=
  (contDiff_coordinateIterate hf cs).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_coordinateIterate hfc cs)

/-- A scalar dilation contributes one factor to each coordinate derivative
(`paper/main.tex:1005–1008`). -/
theorem coordinateDerivative_const_mul_comp_smul {f : Vec d → ℝ}
    (hf : ContDiff ℝ 1 f) (i : Fin d) (c a : ℝ) (x : Vec d) :
    coordinateDerivative i (fun y => c * f (a • y)) x =
      c * a * coordinateDerivative i f (a • x) := by
  have hdiff : DifferentiableAt ℝ (fun y => f (a • y)) x :=
    ((hf.differentiable one_ne_zero).comp
      (by fun_prop : Differentiable ℝ fun y : Vec d => a • y)) x
  unfold coordinateDerivative
  rw [fderiv_const_mul hdiff c, fderiv_comp_smul]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- The exact scaling formula for any iterated coordinate derivative
(`paper/main.tex:1005–1008`). -/
theorem coordinateIterate_const_mul_comp_smul {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (cs : List (Fin d)) (c a : ℝ) :
    coordinateIterate cs (fun y => c * f (a • y)) =
      fun y => c * a ^ cs.length * coordinateIterate cs f (a • y) := by
  induction cs with
  | nil => simp only [coordinateIterate, List.length_nil, pow_zero, mul_one]
  | cons i rest ih =>
    change coordinateDerivative i (coordinateIterate rest (fun y => c * f (a • y))) = _
    rw [ih]
    funext x
    rw [coordinateDerivative_const_mul_comp_smul
      ((contDiff_coordinateIterate hf rest).of_le (by exact_mod_cast le_top))]
    simp only [List.length_cons, coordinateIterate, pow_succ]
    ring

/-- Exact `L¹` scaling of every coordinate derivative of
`K_r(x) = r^{2-d} K(x/r)` (`paper/main.tex:1005–1008`). -/
theorem integral_abs_coordinateIterate_scaled {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hd : 2 ≤ d) {r : ℝ} (hr : 0 < r)
    (cs : List (Fin d)) :
    (∫ x : Vec d, |coordinateIterate cs
      (fun y => (r ^ (d - 2))⁻¹ * f (r⁻¹ • y)) x|) =
        r ^ 2 / r ^ cs.length * ∫ x : Vec d, |coordinateIterate cs f x| := by
  rw [coordinateIterate_const_mul_comp_smul hf]
  simp only [abs_mul, abs_inv, abs_pow, abs_of_pos hr]
  rw [integral_const_mul]
  have hchange := Measure.integral_comp_smul (volume : Measure (Vec d))
    (fun x : Vec d => |coordinateIterate cs f x|) r⁻¹
  have habs : |((r⁻¹) ^ d)⁻¹| = r ^ d := by
    rw [inv_pow, inv_inv, abs_of_pos (pow_pos hr d)]
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, smul_eq_mul, habs] at hchange
  rw [hchange]
  have hdim : r ^ d = r ^ (d - 2) * r ^ 2 := by
    rw [← pow_add, Nat.sub_add_cancel hd]
  rw [hdim, inv_pow]
  field_simp

end EinsteinRelation.Correctors.KernelCalculus
