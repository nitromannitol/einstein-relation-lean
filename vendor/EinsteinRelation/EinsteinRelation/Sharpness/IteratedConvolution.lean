import EinsteinRelation.Sharpness.ConvolutionDerivative
import EinsteinRelation.Sharpness.CoordinateIterates
import EinsteinRelation.Sharpness.OuterConvolution
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Deterministic bounds on iterated coordinate derivatives of the outer convolution

Source: `paper/main.tex`, proof of Proposition 7.1, Step 1, lines 1212–1216. For a smooth,
compactly supported `ζ` and a continuous `H`, every iterated coordinate derivative of the outer
convolution `z ↦ ∫ ζ(y) H(z - y) dy` falls on the kernel `ζ`. The amplitude bound `|H| ≤ 1`
then bounds each such derivative by the `L¹` norm of the same derivative of `ζ`. The uniform
constant is chosen before `H`, so it does not depend on any noise sample or law. The results are
deterministic: they assume no stationarity, finite range, Gaussian law, or nondegeneracy.
-/

open MeasureTheory

namespace EinsteinRelation.Sharpness

/-- Function-level form of the iterated outer-convolution identity, proved by induction on the
list of coordinates. The kernel `ζ` is fixed, so each step applies the one-step identity to the
kernel `iteratedCoordinateDerivative is ζ`. -/
private theorem iteratedCoordinateDerivative_outer_convolution_fun {d : ℕ} (ζ H : Vec d → ℝ)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hζc : HasCompactSupport ζ) (hH : Continuous H)
    (is : List (Fin d)) :
    iteratedCoordinateDerivative is (fun z : Vec d => ∫ y : Vec d, ζ y * H (z-y)) =
      fun x : Vec d => ∫ y : Vec d, iteratedCoordinateDerivative is ζ y * H (x-y) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    show coordinateDerivative i
        (iteratedCoordinateDerivative is (fun z : Vec d => ∫ y : Vec d, ζ y * H (z-y))) =
      fun x : Vec d =>
        ∫ y : Vec d, coordinateDerivative i (iteratedCoordinateDerivative is ζ) y * H (x-y)
    rw [ih]
    funext x
    exact coordinateDerivative_outer_convolution (iteratedCoordinateDerivative is ζ) H
      (contDiff_iteratedCoordinateDerivative ζ hζ is)
      (hasCompactSupport_iteratedCoordinateDerivative ζ hζc is) hH i x

/-- Source: `paper/main.tex`, Proposition 7.1, Step 1, lines 1212–1216. For a smooth, compactly
supported `ζ` and a continuous `H`, each iterated coordinate derivative of the outer convolution
`z ↦ ∫ ζ(y) H(z - y) dy` is the outer convolution of the same iterated derivative of `ζ` with
`H`. -/
theorem iteratedCoordinateDerivative_outer_convolution {d : ℕ} (ζ H : Vec d → ℝ)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hζc : HasCompactSupport ζ) (hH : Continuous H)
    (is : List (Fin d)) (x : Vec d) :
    iteratedCoordinateDerivative is (fun z : Vec d => ∫ y : Vec d, ζ y * H (z-y)) x =
      ∫ y : Vec d, iteratedCoordinateDerivative is ζ y * H (x-y) :=
  congrFun (iteratedCoordinateDerivative_outer_convolution_fun ζ H hζ hζc hH is) x

/-- Source: `paper/main.tex`, Proposition 7.1, Step 1, lines 1212–1216. If `|H| ≤ 1`, every iterated
coordinate derivative of the outer convolution `z ↦ ∫ ζ(y) H(z - y) dy` is bounded pointwise by the
`L¹` norm of the same iterated derivative of `ζ`. No derivative of `H` is assumed. -/
theorem abs_iteratedCoordinateDerivative_outer_convolution_le {d : ℕ} (ζ H : Vec d → ℝ)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hζc : HasCompactSupport ζ) (hH : Continuous H)
    (hb : ∀ y, |H y| ≤ 1) (is : List (Fin d)) (x : Vec d) :
    |iteratedCoordinateDerivative is (fun z : Vec d => ∫ y : Vec d, ζ y * H (z-y)) x| ≤
      ∫ y : Vec d, |iteratedCoordinateDerivative is ζ y| := by
  rw [iteratedCoordinateDerivative_outer_convolution ζ H hζ hζc hH is x]
  exact abs_outer_convolution_le (iteratedCoordinateDerivative is ζ) H
    (contDiff_iteratedCoordinateDerivative ζ hζ is).continuous
    (hasCompactSupport_iteratedCoordinateDerivative ζ hζc is) hH hb x

/-- Source: `paper/main.tex`, Proposition 7.1, Step 1, lines 1212–1216. For a smooth, compactly
supported `ζ` and every bounded continuous field `H`, the iterated coordinate derivatives of the
outer convolution are bounded uniformly in `x`. The constant is the `L¹` norm of the absolute
iterated derivative of `ζ`. It depends only on `ζ` and the coordinate list, and it is chosen
before `H`. -/
theorem exists_uniform_outer_derivative_bound {d : ℕ} (ζ : Vec d → ℝ)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hζc : HasCompactSupport ζ) (is : List (Fin d)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ H : Vec d → ℝ, Continuous H → (∀ y, |H y| ≤ 1) →
      ∀ x : Vec d,
      |iteratedCoordinateDerivative is (fun z : Vec d => ∫ y : Vec d, ζ y * H (z-y)) x| ≤ C := by
  refine ⟨(∫ y : Vec d, |iteratedCoordinateDerivative is ζ y|), ?_, ?_⟩
  · exact integral_nonneg fun y => abs_nonneg _
  · intro H hH hb x
    exact abs_iteratedCoordinateDerivative_outer_convolution_le ζ H hζ hζc hH hb is x

end EinsteinRelation.Sharpness
