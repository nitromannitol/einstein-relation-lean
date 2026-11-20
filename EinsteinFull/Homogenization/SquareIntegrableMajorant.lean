import EinsteinFull.Homogenization.MajorantProbability

/-!
# Square-integrability from a majorant

An almost everywhere measurable observable dominated by a square-integrable
majorant has an integrable square with the corresponding moment bound.
-/

open MeasureTheory

namespace EinsteinFull.Homogenization

/-- An almost everywhere measurable nonnegative observable dominated by a
square-integrable majorant has a bounded and integrable square. -/
theorem memLp_and_integral_sq_le_of_majorant
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (f H : Ω → ℝ) (C B : ℝ)
    (hC : 0 ≤ C) (hf : ∀ a, 0 ≤ f a) (hH : ∀ a, 0 ≤ H a)
    (hbound : ∀ a, f a ≤ C * H a) (hmeas : AEMeasurable f P) (hmem : MemLp H 2 P)
    (hsecond : (∫ a, (H a) ^ 2 ∂P) ≤ B) :
    MemLp f 2 P ∧ Integrable (fun a => (f a) ^ 2) P ∧
      (∫ a, (f a) ^ 2 ∂P) ≤ C ^ 2 * B := by
  have hCmem : MemLp (fun a => C * H a) 2 P := hmem.const_mul C
  have hfm : MemLp f 2 P := hCmem.mono' hmeas.aestronglyMeasurable (by
    filter_upwards with a
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hf a)] using hbound a)
  have hsq (a) : (f a) ^ 2 ≤ C ^ 2 * (H a) ^ 2 := by
    have hCH := mul_nonneg hC (hH a)
    nlinarith [hf a, hbound a, sq_nonneg (C * H a - f a)]
  refine ⟨hfm, hfm.integrable_sq, ?_⟩
  calc
    _ ≤ ∫ a, C ^ 2 * (H a) ^ 2 ∂P :=
      integral_mono hfm.integrable_sq (hmem.integrable_sq.const_mul _) hsq
    _ = C ^ 2 * ∫ a, (H a) ^ 2 ∂P := integral_const_mul _ _
    _ ≤ C ^ 2 * B := mul_le_mul_of_nonneg_left hsecond (sq_nonneg C)

end EinsteinFull.Homogenization
