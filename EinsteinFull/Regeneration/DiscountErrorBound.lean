import EinsteinFull.Regeneration.GeometricTailMoment

/-!
# Discount error under a first-moment bound

For a payoff between zero and one, the error from exponential discounting
is at most the discount multiplied by the expected nonnegative duration.
-/

open MeasureTheory

namespace EinsteinFull.Regeneration

/-- A bounded nonnegative payoff has a discount error controlled by the mean duration. -/
theorem integral_discount_error_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (S F : Ω → ℝ)
    (hS : Measurable S) (hSi : Integrable S P) (hS0 : ∀ ω, 0 ≤ S ω)
    (hF : Measurable F) (hF0 : ∀ ω, 0 ≤ F ω) (hF1 : ∀ ω, F ω ≤ 1)
    (a : ℝ) (ha : 0 ≤ a) :
    0 ≤ (∫ ω, F ω ∂P) - ∫ ω, Real.exp (-(a * S ω)) * F ω ∂P ∧
      (∫ ω, F ω ∂P) - ∫ ω, Real.exp (-(a * S ω)) * F ω ∂P ≤
        a * ∫ ω, S ω ∂P := by
  let D : Ω → ℝ := fun ω => Real.exp (-(a * S ω)) * F ω
  have hD : Measurable D := (Real.measurable_exp.comp ((measurable_const.mul hS).neg)).mul hF
  have hD0 : ∀ ω, 0 ≤ D ω := fun ω => mul_nonneg (Real.exp_pos _).le (hF0 ω)
  have hDF : ∀ ω, D ω ≤ F ω := by
    intro ω
    apply (mul_le_mul_of_nonneg_right ?_ (hF0 ω)).trans_eq (one_mul _)
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg ha (hS0 ω)))
  have hFi : Integrable F P := Integrable.of_bound hF.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hF0 ω)]
      exact hF1 ω)
  have hDi : Integrable D P := Integrable.of_bound hD.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hD0 ω)]
      exact (hDF ω).trans (hF1 ω))
  have hpoint : ∀ ω, F ω - D ω ≤ a * S ω := by
    intro ω
    have he := Real.add_one_le_exp (-(a * S ω))
    have haux : 0 ≤ 1 - Real.exp (-(a * S ω)) := by
      have hw := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg ha (hS0 ω)))
      linarith
    have hm := mul_le_mul_of_nonneg_left (hF1 ω) haux
    dsimp [D]
    nlinarith
  constructor
  · exact sub_nonneg.mpr (integral_mono_ae hDi hFi (Filter.Eventually.of_forall hDF))
  · rw [← integral_sub hFi hDi, ← integral_const_mul]
    exact integral_mono_ae (hFi.sub hDi) (hSi.const_mul a) (Filter.Eventually.of_forall hpoint)

end EinsteinFull.Regeneration
