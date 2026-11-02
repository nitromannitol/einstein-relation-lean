import EinsteinRelation.Environment.Basic
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith

/-! # Deterministic outer convolution with a compactly supported kernel

Source: `paper/main.tex`, proof of Proposition 7.1, Step 1, lines 1212–1216. The field
`h ≔ ζ * tanh(K * W)` has each derivative bounded deterministically because the outer
convolution with the compactly supported, smooth function `ζ` smooths a bounded
continuous field.

Here `*` is the ordinary Lebesgue convolution on `Vec d`, with respect to the measure
`volume`. The results are deterministic: they assume no stationarity, finite range,
Gaussian law, or uniform derivative bound.
-/

open MeasureTheory
open scoped Convolution

namespace EinsteinRelation.Sharpness

/-- `Real.tanh` is continuous, as the quotient of the continuous `sinh` by the everywhere
positive `cosh`. -/
private theorem continuous_realTanh : Continuous Real.tanh := by
  have h : Real.tanh = fun t => Real.sinh t / Real.cosh t :=
    funext Real.tanh_eq_sinh_div_cosh
  rw [h]
  exact Real.continuous_sinh.div₀ Real.continuous_cosh (fun t => (Real.cosh_pos t).ne')

/-- `|tanh t| ≤ 1`. The pinned Mathlib has no such lemma, so it is derived from
`|sinh t| ≤ cosh t`, which holds because `cosh t ± sinh t = exp (±t) > 0`. -/
private theorem abs_realTanh_le_one (t : ℝ) : |Real.tanh t| ≤ 1 := by
  rw [Real.tanh_eq_sinh_div_cosh, abs_div, abs_of_pos (Real.cosh_pos t),
    div_le_one (Real.cosh_pos t), abs_le]
  constructor
  · linarith [Real.cosh_add_sinh t, Real.exp_pos t]
  · linarith [Real.cosh_sub_sinh t, Real.exp_pos (-t)]

/-- Source: `paper/main.tex`, Proposition 7.1, Step 1, lines 1212–1216. For a smooth,
compactly supported `ζ` and a bounded continuous `H`, the Lebesgue convolution
`x ↦ ∫ ζ(y) H(x - y) dy` is `C^∞` on `Vec d`. -/
theorem contDiff_outer_convolution {d : ℕ} (ζ H : Vec d → ℝ)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hζc : HasCompactSupport ζ) (hH : Continuous H) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec d => ∫ y : Vec d, ζ y * H (x - y)) := by
  have hfun : (fun x : Vec d => ∫ y : Vec d, ζ y * H (x - y)) =
      ζ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] H := by
    funext x
    simp only [convolution_lsmul, smul_eq_mul]
  rw [hfun]
  exact HasCompactSupport.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hζc hζ
    hH.locallyIntegrable

/-- Source: `paper/main.tex`, Proposition 7.1, Step 1, lines 1212–1216. If `|H| ≤ 1`, the
Lebesgue convolution of a continuous compactly supported `ζ` with `H` is bounded pointwise
by the `L¹` norm of `ζ`. -/
theorem abs_outer_convolution_le {d : ℕ} (ζ H : Vec d → ℝ)
    (hζ : Continuous ζ) (hζc : HasCompactSupport ζ) (hH : Continuous H)
    (hb : ∀ x, |H x| ≤ 1) (x : Vec d) :
    |∫ y : Vec d, ζ y * H (x - y)| ≤ ∫ y : Vec d, |ζ y| := by
  -- `hb` gives the pointwise bound. `hH` makes the product `ζ y * H (x - y)` continuous
  -- with compact support, hence integrable, which `integral_mono` needs.
  have hζi : Integrable ζ volume := hζ.integrable_of_hasCompactSupport hζc
  have hcont : Continuous (fun y : Vec d => x - y) := continuous_const.sub continuous_id
  have hprodCont : Continuous (fun y : Vec d => ζ y * H (x - y)) :=
    hζ.mul (hH.comp hcont)
  have hprodComp : HasCompactSupport (fun y : Vec d => ζ y * H (x - y)) :=
    hζc.mul_right
  have hprodInt : Integrable (fun y : Vec d => ζ y * H (x - y)) volume :=
    hprodCont.integrable_of_hasCompactSupport hprodComp
  have hpt : ∀ y : Vec d, ‖ζ y * H (x - y)‖ ≤ |ζ y| := fun y => by
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (hb _)
  calc |∫ y : Vec d, ζ y * H (x - y)|
      = ‖∫ y : Vec d, ζ y * H (x - y)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ y : Vec d, ‖ζ y * H (x - y)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y : Vec d, |ζ y| :=
        integral_mono hprodInt.norm hζi.abs hpt

/-- Source: `paper/main.tex`, Proposition 7.1, Step 1, lines 1212–1216, with the bounded
continuous field `tanh ∘ G` in place of `H`, as in `h = ζ * tanh(K * W)`. -/
theorem contDiff_outer_convolution_tanh {d : ℕ} (ζ G : Vec d → ℝ)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hζc : HasCompactSupport ζ) (hG : Continuous G) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec d => ∫ y : Vec d, ζ y * Real.tanh (G (x - y))) :=
  contDiff_outer_convolution ζ (fun z => Real.tanh (G z)) hζ hζc
    (continuous_realTanh.comp hG)

/-- Source: `paper/main.tex`, Proposition 7.1, Step 1, lines 1212–1216, with `tanh ∘ G` in
place of `H`. Since `|tanh| ≤ 1` deterministically, the bound holds for every `x`. -/
theorem abs_outer_convolution_tanh_le {d : ℕ} (ζ G : Vec d → ℝ)
    (hζ : Continuous ζ) (hζc : HasCompactSupport ζ) (hG : Continuous G) (x : Vec d) :
    |∫ y : Vec d, ζ y * Real.tanh (G (x - y))| ≤ ∫ y : Vec d, |ζ y| :=
  abs_outer_convolution_le ζ (fun z => Real.tanh (G z)) hζ hζc
    (continuous_realTanh.comp hG) (fun z => abs_realTanh_le_one (G z)) x

end EinsteinRelation.Sharpness
