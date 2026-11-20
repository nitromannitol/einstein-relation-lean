import Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.Additivity.AnalyticInequalities
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Weighted square-root estimates

Finite weighted sums of square roots satisfy a Cauchy–Schwarz estimate. This
form is useful for the multiscale flatness argument in Armstrong, Kuusi and
Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Chapter 2.
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open Book.Ch05.Section53.JUpperBoundWeakNorms

/-- The square of a finite weighted sum of square roots is integrable and is
bounded in expectation by the weighted sum of expectations. -/
theorem integrable_and_integral_sq_sum_weighted_sqrt_le
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (s : Finset ι) (w : ι → ℝ) (f : ι → Ω → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hf : ∀ i ∈ s, Integrable (f i) P)
    (hf0 : ∀ i ∈ s, ∀ a, 0 ≤ f i a) :
    Integrable (fun a => (∑ i ∈ s, w i * Real.sqrt (f i a)) ^ 2) P ∧
    (∫ a, (∑ i ∈ s, w i * Real.sqrt (f i a)) ^ 2 ∂P) ≤
      (∑ i ∈ s, w i) * ∑ i ∈ s, w i * ∫ a, f i a ∂P := by
  have hsum : MemLp (fun a => ∑ i ∈ s, w i * Real.sqrt (f i a)) 2 P := by
    apply memLp_finsetSum
    intro i hi
    exact (memLp_sqrt_two_of_integrable_of_ae_nonneg (hf i hi)
      (Filter.Eventually.of_forall (hf0 i hi))).const_mul (w i)
  have hsquare := hsum.integrable_sq
  have hright : Integrable (fun a => (∑ i ∈ s, w i) * ∑ i ∈ s, w i * f i a) P :=
    (integrable_finsetSum s (fun i hi => (hf i hi).const_mul (w i))).const_mul _
  refine ⟨hsquare, ?_⟩
  have hpoint (a : Ω) : (∑ i ∈ s, w i * Real.sqrt (f i a)) ^ 2 ≤
      (∑ i ∈ s, w i) * ∑ i ∈ s, w i * f i a := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s (r := fun i => w i * Real.sqrt (f i a))
      (f := w) (g := fun i => w i * f i a) hw
      (fun i hi => mul_nonneg (hw i hi) (hf0 i hi a))
    intro i hi
    have h := Real.sq_sqrt (hf0 i hi a)
    nlinarith [sq_nonneg (w i)]
  calc
    _ ≤ ∫ a, (∑ i ∈ s, w i) * ∑ i ∈ s, w i * f i a ∂P :=
      integral_mono hsquare hright hpoint
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum s (fun i hi => (hf i hi).const_mul (w i))]
      simp only [integral_const_mul]

end EinsteinFull.Homogenization
