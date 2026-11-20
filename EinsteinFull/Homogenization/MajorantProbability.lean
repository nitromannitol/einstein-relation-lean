import EinsteinFull.Homogenization.SourceOptimizerFlatnessDecay

/-!
# Probability bounds from square-integrable majorants

A pointwise bound by a square-integrable random variable controls the measure
of a level set, without requiring the dominated observable to be measurable.
-/

open MeasureTheory

namespace EinsteinFull.Homogenization

/-- A square-integrable majorant controls level-set probabilities. -/
theorem measureReal_ge_le_of_squareIntegrable_majorant
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (f H : Ω → ℝ) (C ε B : ℝ) (hC : 0 ≤ C) (hε : 0 < ε)
    (hf : ∀ a, 0 ≤ f a) (hH : ∀ a, 0 ≤ H a)
    (hbound : ∀ a, f a ≤ C * H a) (hmem : MemLp H 2 P)
    (hsecond : (∫ a, (H a) ^ 2 ∂P) ≤ B) :
    P.real {a | ε ≤ f a} ≤ (C ^ 2 * B) / ε ^ 2 := by
  have hsubset : {a | ε ≤ f a} ⊆ {a | ε ^ 2 ≤ C ^ 2 * (H a) ^ 2} := by
    intro a ha
    have hCH := mul_nonneg hC (hH a)
    simp only [Set.mem_setOf_eq] at ha ⊢
    nlinarith [hf a, hbound a, sq_nonneg (C * H a - f a)]
  have hnonneg : 0 ≤ᵐ[P] (fun a => C ^ 2 * (H a) ^ 2) :=
    Filter.Eventually.of_forall (fun a => mul_nonneg (sq_nonneg C) (sq_nonneg (H a)))
  have hint : Integrable (fun a => C ^ 2 * (H a) ^ 2) P := hmem.integrable_sq.const_mul _
  have hmarkov := mul_meas_ge_le_integral_of_nonneg hnonneg hint (ε ^ 2)
  rw [integral_const_mul] at hmarkov
  have hsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  apply (le_div_iff₀ hsq).2
  calc
    _ ≤ ε ^ 2 * P.real {a | ε ^ 2 ≤ C ^ 2 * (H a) ^ 2} := by
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_left (measureReal_mono (μ := P) hsubset (measure_ne_top P _)) hsq.le
    _ ≤ C ^ 2 * ∫ a, (H a) ^ 2 ∂P := hmarkov
    _ ≤ C ^ 2 * B := mul_le_mul_of_nonneg_left hsecond (sq_nonneg C)

end EinsteinFull.Homogenization
