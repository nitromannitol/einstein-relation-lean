import EinsteinFull.Homogenization.SourceOptimizerFlatnessGeometric

/-!
# Outer second moments from measurable majorants

A square-integrable majorant bounds the extended nonnegative integral of a
nonnegative observable, without requiring a measurable representative for the
observable itself.
-/

open MeasureTheory

namespace EinsteinFull.Homogenization

/-- A nonnegative pointwise observable dominated by a square-integrable
majorant has a bounded extended nonnegative second moment. -/
theorem lintegral_sq_le_of_squareIntegrable_majorant
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (f H : Ω → ℝ) (C B : ℝ)
    (hC : 0 ≤ C) (hf : ∀ a, 0 ≤ f a) (hH : ∀ a, 0 ≤ H a)
    (hbound : ∀ a, f a ≤ C * H a) (hmem : MemLp H 2 P)
    (hsecond : (∫ a, (H a) ^ 2 ∂P) ≤ B) :
    (∫⁻ a, ENNReal.ofReal ((f a) ^ 2) ∂P) ≤ ENNReal.ofReal (C ^ 2 * B) := by
  have hint : Integrable (fun a => C ^ 2 * (H a) ^ 2) P := hmem.integrable_sq.const_mul _
  have hnonneg : 0 ≤ᵐ[P] (fun a => C ^ 2 * (H a) ^ 2) :=
    Filter.Eventually.of_forall (fun a => mul_nonneg (sq_nonneg C) (sq_nonneg (H a)))
  calc
    _ ≤ ∫⁻ a, ENNReal.ofReal (C ^ 2 * (H a) ^ 2) ∂P := by
      apply lintegral_mono
      intro a
      apply ENNReal.ofReal_le_ofReal
      have hCH := mul_nonneg hC (hH a)
      nlinarith [hf a, hbound a, sq_nonneg (C * H a - f a)]
    _ = ENNReal.ofReal (C ^ 2 * ∫ a, (H a) ^ 2 ∂P) := by
      rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg, integral_const_mul]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hsecond (sq_nonneg C))

end EinsteinFull.Homogenization
