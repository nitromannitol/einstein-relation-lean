import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Bounded data averaged against a nonnegative unit-mass kernel

Source: `paper/main.tex:850`; AKM Appendix E (E.4), printed p. 499.
This is an integral lemma for a specified kernel, with no new literature
input or existence assertion.
-/

open MeasureTheory
namespace EinsteinRelation.Correctors

/-- Positivity and unit mass bound a kernel average of a bounded scalar datum.
Source: paper/main.tex:850; AKM Appendix E (E.4), p. 499. -/
theorem paired_kernel_average_bound {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {k f : X → ℝ} {B : ℝ}
    (hk : Integrable k μ) (hk0 : ∀ᵐ x ∂μ, 0 ≤ k x)
    (hk1 : (∫ x, k x ∂μ) = 1)
    (hf : AEStronglyMeasurable f μ)
    (hbound : ∀ᵐ x ∂μ, |f x| ≤ B) :
    Integrable (fun x => k x * f x) μ ∧ |∫ x, k x * f x ∂μ| ≤ B := by
  have hnorm : ∀ᵐ x ∂μ, ‖k x * f x‖ ≤ k x * B := by
    filter_upwards [hk0, hbound] with x hx hfx
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hx, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hfx hx
  have hi : Integrable (fun x => k x * f x) μ :=
    (hk.mul_const B).mono' (hk.aestronglyMeasurable.mul hf) hnorm
  refine ⟨hi, ?_⟩
  calc
    |∫ x, k x * f x ∂μ| ≤ ∫ x, k x * B ∂μ := by
      simpa only [Real.norm_eq_abs] using
        norm_integral_le_of_norm_le (hk.mul_const B) hnorm
    _ = B := by rw [integral_mul_const, hk1, one_mul]

end EinsteinRelation.Correctors
