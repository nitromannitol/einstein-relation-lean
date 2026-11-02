import EinsteinRelation.Sharpness.NoiseField
import EinsteinRelation.Sharpness.ConvolutionDerivative
import EinsteinRelation.TimeChange.EuclideanTransport
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-! # Uniform gradient scale for the smoothed noise field

Source: `paper/main.tex`, proof of Proposition 7.1, Step 1, lines 1212–1218. The field
`h ≔ ζ * tanh(K * W)` (lines 1212–1216) has every coordinate derivative bounded by the `L¹`
norm of the corresponding coordinate derivative of the fixed outer kernel `ζ`, uniformly in the
kernel `K`, the sample `W`, and the point `x`. The scale `ε` (line 1218) is chosen from `ζ` alone,
before any kernel, sample, or point, so that `ε h` has Euclidean gradient at most `1/4`.

All geometric norms are the explicit `euclideanNorm` and `euclideanSq`, never the default
supremum norm on `Vec d`. The argument is uniform in `d`: for `d = 0` the coordinate sums are
empty and the bound holds trivially. No stationarity, finite range, or Gaussian law is used.
-/

open MeasureTheory
open EinsteinRelation.TimeChange (euclideanNorm_smul)

namespace EinsteinRelation.Sharpness

/-- `Real.tanh` is continuous, as the quotient of the continuous `sinh` by the everywhere
positive `cosh`. -/
private theorem gradientScale_continuous_tanh : Continuous Real.tanh := by
  have h : Real.tanh = fun t => Real.sinh t / Real.cosh t :=
    funext Real.tanh_eq_sinh_div_cosh
  rw [h]
  exact Real.continuous_sinh.div₀ Real.continuous_cosh (fun t => (Real.cosh_pos t).ne')

/-- `|tanh t| ≤ 1`, from `|sinh t| ≤ cosh t`, since `cosh t ± sinh t = exp (±t) > 0`. -/
private theorem gradientScale_abs_tanh_le_one (t : ℝ) : |Real.tanh t| ≤ 1 := by
  rw [Real.tanh_eq_sinh_div_cosh, abs_div, abs_of_pos (Real.cosh_pos t),
    div_le_one (Real.cosh_pos t), abs_le]
  constructor
  · linarith [Real.cosh_add_sinh t, Real.exp_pos t]
  · linarith [Real.cosh_sub_sinh t, Real.exp_pos (-t)]

/-- The sum of squared coordinate `L¹` norms `∑ᵢ (∫ |∂ᵢ ζ|)²` of the fixed kernel `ζ`. It depends
on `ζ` alone, so it fixes the scale before any kernel `K`, sample `W`, or point `x`. -/
private noncomputable def gradientScaleBound {d : ℕ} (ζ : NoiseTest d) : ℝ :=
  ∑ i : Fin d, (∫ y : Vec d, |coordinateDerivative i (ζ : Vec d → ℝ) y|) ^ 2

private theorem gradientScaleBound_nonneg {d : ℕ} (ζ : NoiseTest d) :
    0 ≤ gradientScaleBound ζ := by
  unfold gradientScaleBound
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-- If `|a| ≤ b`, then `a * a ≤ b ^ 2`. -/
private theorem gradientScale_mul_self_le_sq {a b : ℝ} (h : |a| ≤ b) : a * a ≤ b ^ 2 :=
  calc a * a = |a| * |a| := (abs_mul_abs_self a).symm
    _ ≤ b * b := mul_self_le_mul_self (abs_nonneg a) h
    _ = b ^ 2 := (pow_two b).symm

/-- Each coordinate derivative of the literal field `ζ * tanh(K * W)` is bounded by the `L¹` norm
of the coordinate derivative of `ζ`. The bound is uniform in `K`, `W`, and `x`, because the
derivative falls on `ζ` and `|tanh| ≤ 1`. -/
private theorem gradientScale_abs_coordinateDerivative_le {d : ℕ} (ζ K : NoiseTest d)
    (W : NoiseSample d) (i : Fin d) (x : Vec d) :
    |coordinateDerivative i (smoothedNoiseField ζ K W) x| ≤
      ∫ y : Vec d, |coordinateDerivative i (ζ : Vec d → ℝ) y| :=
  abs_coordinateDerivative_outer_convolution_le (ζ : Vec d → ℝ)
    (fun z : Vec d => Real.tanh (mollifiedNoise W K z)) ζ.contDiff ζ.hasCompactSupport
    (gradientScale_continuous_tanh.comp (continuous_mollifiedNoise W K))
    (fun z => gradientScale_abs_tanh_le_one (mollifiedNoise W K z)) i x

/-- The gradient of a scalar multiple `c * f` is `c` times the gradient of `f` at a point of
differentiability. This is proved from the Fréchet derivative, not assumed. -/
private theorem gradientScale_gradient_const_mul {d : ℕ} (c : ℝ) (f : Vec d → ℝ) (x : Vec d)
    (hf : DifferentiableAt ℝ f x) :
    gradient (fun y => c * f y) x = c • gradient f x := by
  funext i
  show coordinateDerivative i (fun y => c * f y) x = c * coordinateDerivative i f x
  unfold coordinateDerivative
  rw [fderiv_const_mul hf c, ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- The squared Euclidean norm of the gradient of the literal field is bounded by
`gradientScaleBound ζ`, uniformly in `K`, `W`, and `x`. -/
private theorem gradientScale_euclideanSq_le {d : ℕ} (ζ K : NoiseTest d)
    (W : NoiseSample d) (x : Vec d) :
    euclideanSq (gradient (smoothedNoiseField ζ K W) x) ≤ gradientScaleBound ζ := by
  unfold euclideanSq dot gradientScaleBound
  exact Finset.sum_le_sum fun i _ =>
    gradientScale_mul_self_le_sq (gradientScale_abs_coordinateDerivative_le ζ K W i x)

/-- The Euclidean norm of the gradient of the literal field is at most `gradientScaleBound ζ + 1`,
uniformly in `K`, `W`, and `x`. -/
private theorem gradientScale_euclideanNorm_le {d : ℕ} (ζ K : NoiseTest d)
    (W : NoiseSample d) (x : Vec d) :
    euclideanNorm (gradient (smoothedNoiseField ζ K W) x) ≤ gradientScaleBound ζ + 1 := by
  have hsq := gradientScale_euclideanSq_le ζ K W x
  have hS := gradientScaleBound_nonneg ζ
  unfold euclideanNorm
  rw [Real.sqrt_le_iff]
  exact ⟨by linarith, by nlinarith [sq_nonneg (gradientScaleBound ζ)]⟩

/-- Source: `paper/main.tex`, proof of Proposition 7.1, Step 1, lines 1212–1218. For the fixed
outer kernel `ζ`, there is a positive scale `ε`, chosen before any kernel `K`, sample `W`, or
point `x`, such that the scaled literal field `ε * ζ * tanh(K * W)` has Euclidean gradient at most
`1/4` everywhere. The construction uses no stationarity, finite range, or Gaussian law. -/
theorem exists_uniform_smoothedNoiseField_gradient_scale {d : ℕ} (ζ : NoiseTest d) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (K : NoiseTest d) (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * smoothedNoiseField ζ K W y) x) ≤ (1/4 : ℝ) := by
  have hS := gradientScaleBound_nonneg ζ
  have hpos : (0 : ℝ) < 4 * (gradientScaleBound ζ + 1) := by linarith
  have hε0 : (0 : ℝ) < 1 / (4 * (gradientScaleBound ζ + 1)) := div_pos one_pos hpos
  have hεS : 1 / (4 * (gradientScaleBound ζ + 1)) * (gradientScaleBound ζ + 1) = 1 / 4 := by
    linear_combination (1 / 4 : ℝ) * one_div_mul_cancel hpos.ne'
  refine ⟨1 / (4 * (gradientScaleBound ζ + 1)), hε0, ?_⟩
  intro K W x
  have hdiff : DifferentiableAt ℝ (smoothedNoiseField ζ K W) x :=
    (contDiff_smoothedNoiseField ζ K W).differentiable (by simp) x
  rw [gradientScale_gradient_const_mul (1 / (4 * (gradientScaleBound ζ + 1)))
      (smoothedNoiseField ζ K W) x hdiff, euclideanNorm_smul, abs_of_pos hε0]
  calc 1 / (4 * (gradientScaleBound ζ + 1)) *
        euclideanNorm (gradient (smoothedNoiseField ζ K W) x)
      ≤ 1 / (4 * (gradientScaleBound ζ + 1)) * (gradientScaleBound ζ + 1) :=
        mul_le_mul_of_nonneg_left (gradientScale_euclideanNorm_le ζ K W x) hε0.le
    _ = 1 / 4 := hεS

end EinsteinRelation.Sharpness
