import EinsteinRelation.Calculus.HorizontalCore
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Horizontal regularization: soft truncation of observables

Source `paper/main.tex` lines 634–638 (second assertion of `entropy.divergence`). The regularization
behind `HorizontalSmoothApproximation` truncates the components of a horizontally mollified field
before smoothing again. This file proves the truncation step on its own:

* `softTruncation M x = x / (1 + (x / M)²)`: a smooth profile with derivative
  `softTruncationDeriv M`, bounded by `1` in absolute value. Along `M = n → ∞` it converges to the
  identity, and its derivative converges to `1`.
* Dominated convergence in `L^p`: the truncation error `softTruncation n ∘ F - F` and the derivative
  error `(1 - softTruncationDeriv n ∘ F) * G` tend to zero.
* The chain rule for the horizontal derivative of a truncated observable, at every orbit that is
  differentiable at the origin.

The profile is a choice made here. The truncation only needs a derivative bounded by one that
tends to one, and a value that tends to the identity.
-/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace EinsteinRelation.Entropy

noncomputable section

/-! ### The soft truncation profile -/

/-- Soft truncation at level `M`: `x ↦ x / (1 + (x / M)²)`. The square is written as a product, so
that the product rule computes its derivative. -/
def softTruncation (M x : ℝ) : ℝ := x / (1 + x / M * (x / M))

/-- The derivative of `softTruncation M`: `(1 - (x / M)²) / (1 + (x / M)²)²`. -/
def softTruncationDeriv (M x : ℝ) : ℝ := (1 - x / M * (x / M)) / (1 + x / M * (x / M)) ^ 2

theorem one_add_mul_self_pos (t : ℝ) : 0 < 1 + t * t := by
  linarith [mul_self_nonneg t]

/-- The truncation is dominated by the identity in absolute value. -/
theorem abs_softTruncation_le (M x : ℝ) : |softTruncation M x| ≤ |x| := by
  unfold softTruncation
  rw [abs_div, abs_of_pos (one_add_mul_self_pos (x / M))]
  exact div_le_self (abs_nonneg x) (by linarith [mul_self_nonneg (x / M)])

/-- The truncation error is at most twice the modulus of the identity. -/
theorem abs_softTruncation_sub_le (M x : ℝ) : |softTruncation M x - x| ≤ 2 * |x| := by
  have h := abs_le.1 (abs_softTruncation_le M x)
  rw [abs_le]
  constructor <;> linarith [h.1, h.2, le_abs_self x, le_abs_self (-x), abs_neg x]

/-- Real algebra behind the derivative bound: `|1 - t| ≤ (1 + t)²` for `t ≥ 0`. -/
theorem abs_ratio_le_one {t : ℝ} (ht : 0 ≤ t) : |(1 - t) / (1 + t) ^ 2| ≤ 1 := by
  have h1 : 0 < 1 + t := by linarith
  have hpos : 0 < (1 + t) ^ 2 := pow_pos h1 2
  rw [abs_div, abs_of_pos hpos, div_le_one₀ hpos, abs_le]
  constructor <;> nlinarith [sq_nonneg t]

/-- The derivative of the soft truncation is bounded by one in absolute value. -/
theorem abs_softTruncationDeriv_le_one (M x : ℝ) : |softTruncationDeriv M x| ≤ 1 :=
  abs_ratio_le_one (mul_self_nonneg (x / M))

/-- Hence `1 - softTruncationDeriv` is bounded by two. -/
theorem abs_one_sub_softTruncationDeriv_le (M x : ℝ) :
    |1 - softTruncationDeriv M x| ≤ 2 := by
  have h := abs_le.1 (abs_softTruncationDeriv_le_one M x)
  rw [abs_le]
  constructor <;> linarith [h.1, h.2]

/-- The soft truncation is differentiable with derivative `softTruncationDeriv M`. -/
theorem hasDerivAt_softTruncation (M x : ℝ) :
    HasDerivAt (softTruncation M) (softTruncationDeriv M x) x := by
  have h1 : HasDerivAt (fun y : ℝ => y / M) (1 / M) x := (hasDerivAt_id' x).div_const M
  have h2 : HasDerivAt (fun y : ℝ => y / M * (y / M)) (1 / M * (x / M) + x / M * (1 / M)) x :=
    h1.fun_mul h1
  have h3 : HasDerivAt (fun y : ℝ => 1 + y / M * (y / M))
      (1 / M * (x / M) + x / M * (1 / M)) x :=
    h2.const_add 1
  have h4 : HasDerivAt (fun y : ℝ => y / (1 + y / M * (y / M)))
      ((1 * (1 + x / M * (x / M)) - x * (1 / M * (x / M) + x / M * (1 / M))) /
        (1 + x / M * (x / M)) ^ 2) x :=
    (hasDerivAt_id' x).fun_div h3 (one_add_mul_self_pos (x / M)).ne'
  refine h4.congr_deriv ?_
  unfold softTruncationDeriv
  ring

/-- The soft truncation is continuous. -/
theorem continuous_softTruncation (M : ℝ) : Continuous (softTruncation M) := by
  have hden : Continuous (fun x : ℝ => 1 + x / M * (x / M)) := by fun_prop
  exact continuous_id.div₀ hden (fun x => (one_add_mul_self_pos (x / M)).ne')

/-- The derivative of the soft truncation is continuous. -/
theorem continuous_softTruncationDeriv (M : ℝ) : Continuous (softTruncationDeriv M) := by
  have hnum : Continuous (fun x : ℝ => 1 - x / M * (x / M)) := by fun_prop
  have hden : Continuous (fun x : ℝ => (1 + x / M * (x / M)) ^ 2) := by fun_prop
  exact hnum.div₀ hden (fun x => (pow_pos (one_add_mul_self_pos (x / M)) 2).ne')

theorem measurable_softTruncation (M : ℝ) : Measurable (softTruncation M) :=
  (continuous_softTruncation M).measurable

theorem measurable_softTruncationDeriv (M : ℝ) : Measurable (softTruncationDeriv M) :=
  (continuous_softTruncationDeriv M).measurable

/-! ### Limits as the truncation level tends to infinity -/

/-- The soft truncation at level `n` converges to the identity as `n → ∞`. -/
theorem tendsto_softTruncation (x : ℝ) :
    Tendsto (fun n : ℕ => softTruncation (n : ℝ) x) atTop (𝓝 x) := by
  have hT : Tendsto (fun n : ℕ => x / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat x
  have hS : Tendsto (fun n : ℕ => x / (n : ℝ) * (x / (n : ℝ))) atTop (𝓝 (0 * 0)) :=
    hT.mul hT
  have hD : Tendsto (fun n : ℕ => 1 + x / (n : ℝ) * (x / (n : ℝ))) atTop (𝓝 (1 + 0 * 0)) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add hS
  have hQ : Tendsto (fun n : ℕ => x / (1 + x / (n : ℝ) * (x / (n : ℝ)))) atTop
      (𝓝 (x / (1 + 0 * 0))) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (𝓝 x)).div hD (by norm_num)
  have h0 : x / (1 + 0 * 0 : ℝ) = x := by norm_num
  rw [h0] at hQ
  exact hQ

/-- The soft truncation derivative at level `n` converges to `1` as `n → ∞`. -/
theorem tendsto_softTruncationDeriv (x : ℝ) :
    Tendsto (fun n : ℕ => softTruncationDeriv (n : ℝ) x) atTop (𝓝 1) := by
  have hT : Tendsto (fun n : ℕ => x / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat x
  have hS : Tendsto (fun n : ℕ => x / (n : ℝ) * (x / (n : ℝ))) atTop (𝓝 (0 * 0)) :=
    hT.mul hT
  have hN : Tendsto (fun n : ℕ => 1 - x / (n : ℝ) * (x / (n : ℝ))) atTop (𝓝 (1 - 0 * 0)) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hS
  have hD : Tendsto (fun n : ℕ => (1 + x / (n : ℝ) * (x / (n : ℝ))) ^ 2) atTop
      (𝓝 ((1 + 0 * 0) ^ 2)) :=
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add hS).pow 2
  have hQ : Tendsto (fun n : ℕ => (1 - x / (n : ℝ) * (x / (n : ℝ))) /
      (1 + x / (n : ℝ) * (x / (n : ℝ))) ^ 2) atTop (𝓝 ((1 - 0 * 0) / (1 + 0 * 0) ^ 2)) :=
    hN.div hD (by norm_num)
  have h1 : (1 - 0 * 0) / (1 + 0 * 0 : ℝ) ^ 2 = 1 := by norm_num
  rw [h1] at hQ
  exact hQ

/-! ### Dominated convergence in `L^p` -/

/-- Dominated convergence for `eLpNorm` along `ℕ`. If the `g n` are measurable, satisfy
`|g n| ≤ 2 |G|` for a fixed `L^p` function `G`, and tend to zero pointwise, then their `L^p` norms
tend to zero. -/
theorem tendsto_eLpNorm_zero_of_dominated {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ∞) {g : ℕ → Ω → ℝ} {G : Ω → ℝ}
    (hG : MemLp G p μ) (hg : ∀ n, Measurable (g n))
    (hbound : ∀ n ω, |g n ω| ≤ 2 * |G ω|) (hlim : ∀ ω, Tendsto (fun n => g n ω) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (g n) p μ) atTop (𝓝 0) := by
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  have hdom : ∀ n ω, ‖g n ω‖ₑ ^ p.toReal ≤ ENNReal.ofReal 2 ^ p.toReal * ‖G ω‖ₑ ^ p.toReal := by
    intro n ω
    rw [← ENNReal.mul_rpow_of_nonneg _ _ hq.le]
    refine ENNReal.rpow_le_rpow ?_ hq.le
    rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs,
      ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 by norm_num)]
    exact ENNReal.ofReal_le_ofReal (hbound n ω)
  have hfin : ∫⁻ ω, ‖G ω‖ₑ ^ p.toReal ∂μ ≠ ∞ := by
    have h2 : ∫⁻ ω, ‖G ω‖ₑ ^ p.toReal ∂μ < ∞ :=
      (hG.integrable_enorm_rpow hp0 hpt).hasFiniteIntegral
    exact h2.ne
  have hr : ENNReal.ofReal 2 ^ p.toReal ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg hq.le ENNReal.ofReal_ne_top
  have hbd : ∫⁻ ω, ENNReal.ofReal 2 ^ p.toReal * ‖G ω‖ₑ ^ p.toReal ∂μ ≠ ∞ := by
    rw [lintegral_const_mul' _ _ hr]
    exact ENNReal.mul_ne_top hr hfin
  have hlimE : ∀ ω, Tendsto (fun n => ‖g n ω‖ₑ ^ p.toReal) atTop (𝓝 0) := by
    intro ω
    have h1 : Tendsto (fun n => ‖g n ω‖ₑ) atTop (𝓝 0) := by
      have h := ((continuous_enorm (E := ℝ)).tendsto (0 : ℝ)).comp (hlim ω)
      simp only [enorm_zero] at h
      exact h
    have h2 := ((ENNReal.continuous_rpow_const (y := p.toReal)).tendsto (0 : ℝ≥0∞)).comp h1
    simp only [ENNReal.zero_rpow_of_pos hq] at h2
    exact h2
  have hint : Tendsto (fun n => ∫⁻ ω, ‖g n ω‖ₑ ^ p.toReal ∂μ) atTop (𝓝 0) := by
    have hmeas : ∀ n, Measurable (fun ω => ‖g n ω‖ₑ ^ p.toReal) := fun n =>
      (hg n).enorm.pow_const _
    have h := tendsto_lintegral_filter_of_dominated_convergence (μ := μ) (l := atTop)
      (F := fun n ω => ‖g n ω‖ₑ ^ p.toReal) (f := fun _ => (0 : ℝ≥0∞))
      (fun ω => ENNReal.ofReal 2 ^ p.toReal * ‖G ω‖ₑ ^ p.toReal)
      (Filter.Eventually.of_forall hmeas)
      (Filter.Eventually.of_forall fun n => Filter.Eventually.of_forall fun ω => hdom n ω)
      hbd (Filter.Eventually.of_forall hlimE)
    simpa only [lintegral_zero] using h
  have hrpow : Tendsto (fun x : ℝ≥0∞ => x ^ (1 / p.toReal)) (𝓝 0) (𝓝 0) := by
    have h := (ENNReal.continuous_rpow_const (y := 1 / p.toReal)).tendsto (0 : ℝ≥0∞)
    simp only [ENNReal.zero_rpow_of_pos (one_div_pos.2 hq)] at h
    exact h
  have hfinal := hrpow.comp hint
  refine Tendsto.congr (fun n => ?_) hfinal
  exact (eLpNorm_eq_lintegral_rpow_enorm_toReal (f := g n) hp0 hpt (hg n).aestronglyMeasurable).symm

/-- The truncation error `softTruncation n ∘ F - F` tends to zero in `L^p`. -/
theorem tendsto_eLpNorm_softTruncation_sub {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ∞) {F : Ω → ℝ} (hF : MemLp F p μ)
    (hFm : Measurable F) :
    Tendsto (fun n : ℕ => eLpNorm (fun ω => softTruncation (n : ℝ) (F ω) - F ω) p μ) atTop
      (𝓝 0) := by
  refine tendsto_eLpNorm_zero_of_dominated (g := fun n ω => softTruncation (n : ℝ) (F ω) - F ω)
    (G := F) hp0 hpt hF (fun n => ((measurable_softTruncation (n : ℝ)).comp hFm).sub hFm)
    (fun n ω => abs_softTruncation_sub_le (n : ℝ) (F ω)) (fun ω => ?_)
  have h := (tendsto_softTruncation (F ω)).sub_const (F ω)
  rw [sub_self] at h
  exact h

/-- The derivative error `(1 - softTruncationDeriv n ∘ F) * G` tends to zero in `L^p`. -/
theorem tendsto_eLpNorm_softTruncationDeriv_error {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ∞) {F G : Ω → ℝ} (hG : MemLp G p μ)
    (hFm : Measurable F) (hGm : Measurable G) :
    Tendsto (fun n : ℕ => eLpNorm (fun ω => (1 - softTruncationDeriv (n : ℝ) (F ω)) * G ω) p μ)
      atTop (𝓝 0) := by
  have hmeas : ∀ n : ℕ, Measurable (fun ω => (1 - softTruncationDeriv (n : ℝ) (F ω)) * G ω) :=
    fun n => ((measurable_const : Measurable fun _ : Ω => (1 : ℝ)).sub
      ((measurable_softTruncationDeriv (n : ℝ)).comp hFm)).mul hGm
  refine tendsto_eLpNorm_zero_of_dominated
    (g := fun n ω => (1 - softTruncationDeriv (n : ℝ) (F ω)) * G ω) (G := G) hp0 hpt hG hmeas
    (fun n ω => ?_) (fun ω => ?_)
  · show |(1 - softTruncationDeriv (n : ℝ) (F ω)) * G ω| ≤ 2 * |G ω|
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (abs_one_sub_softTruncationDeriv_le (n : ℝ) (F ω))
      (abs_nonneg _)
  · have h1 : Tendsto (fun n : ℕ => 1 - softTruncationDeriv (n : ℝ) (F ω)) atTop (𝓝 (1 - 1)) :=
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub
        (tendsto_softTruncationDeriv (F ω))
    have h2 := h1.mul_const (G ω)
    rw [sub_self, zero_mul] at h2
    exact h2

/-! ### Chain rule along orbits -/

/-- The horizontal derivative of a soft truncation of `F` is the truncation derivative times the
horizontal derivative of `F`, at every point `ω` where the orbit of `F` is differentiable at the
origin. -/
theorem horizontalDerivative_softTruncation {d : ℕ} (M : ℝ) (i : Fin d)
    (F : FieldPair d → ℝ) (ω : FieldPair d) (hF : DifferentiableAt ℝ (orbit F ω) 0) :
    horizontalDerivative i (fun η => softTruncation M (F η)) ω =
      softTruncationDeriv M (F ω) * horizontalDerivative i F ω := by
  have hφ : HasDerivAt (softTruncation M) (softTruncationDeriv M (F ω)) (orbit F ω 0) := by
    rw [orbit_zero]
    exact hasDerivAt_softTruncation M (F ω)
  have hcomp := hφ.comp_hasFDerivAt (0 : Vec d) hF.hasFDerivAt
  have key : horizontalDerivative i (fun η => softTruncation M (F η)) ω =
      fderiv ℝ (softTruncation M ∘ orbit F ω) 0 (unitVector i) := rfl
  rw [key, hcomp.fderiv, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rfl

end

end EinsteinRelation.Entropy
