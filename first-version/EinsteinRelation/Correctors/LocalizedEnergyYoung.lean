import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory
namespace EinsteinRelation.Correctors

/-- Integrated square completion for the localized time-derivative energy test.
Source: `paper/main.tex:802`; the AKM Lemma 8.2 time-slice estimate. -/
theorem integral_localized_energy_young {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (c v w : X → ℝ)
    (hvv : Integrable (fun x => (c x)^2 * (v x)^2) μ)
    (hvw : Integrable (fun x => c x * v x * w x) μ)
    (hww : Integrable (fun x => (w x)^2) μ) :
    -2 * (∫ x, (c x)^2 * (v x)^2 ∂μ) -
        4 * (∫ x, c x * v x * w x ∂μ) ≤
      2 * (∫ x, (w x)^2 ∂μ) := by
  have hcv_sq : Integrable (fun x => ((c x * v x) + w x)^2) μ := by
    have h1 : Integrable (fun x => (c x * v x)^2) μ := by
      have : (fun x => (c x * v x)^2) = (fun x => (c x)^2 * (v x)^2) := by
        ext x; ring
      rw [this]
      exact hvv
    have h2 : Integrable (fun x => 2 * (c x * v x * w x)) μ :=
      hvw.const_mul (2 : ℝ)
    have hsum : Integrable (fun x => (c x * v x)^2 + 2 * (c x * v x * w x) + (w x)^2) μ :=
      (h1.add h2).add hww
    have eq : (fun x => ((c x * v x) + w x)^2) =
        (fun x => (c x * v x)^2 + 2 * (c x * v x * w x) + (w x)^2) := by
      ext x; ring
    rw [eq]
    exact hsum
  have h_nonneg : 0 ≤ ∫ x, ((c x * v x) + w x)^2 ∂μ :=
    integral_nonneg fun x => pow_two_nonneg _
  have h_sq_expand : (fun x => ((c x * v x) + w x)^2) =
      (fun x => (c x)^2 * (v x)^2 + 2 * (c x * v x * w x) + (w x)^2) := by
    ext x; ring
  have h_int_expand : (∫ x, ((c x * v x) + w x)^2 ∂μ) =
      (∫ x, (c x)^2 * (v x)^2 ∂μ) + 2 * (∫ x, c x * v x * w x ∂μ) + (∫ x, (w x)^2 ∂μ) := by
    calc
      (∫ x, ((c x * v x) + w x)^2 ∂μ) =
          (∫ x, (c x)^2 * (v x)^2 + 2 * (c x * v x * w x) + (w x)^2 ∂μ) := by
        rw [h_sq_expand]
      _ = (∫ x, ((c x)^2 * (v x)^2 + 2 * (c x * v x * w x)) + (w x)^2 ∂μ) := by ring
      _ = (∫ x, ((c x)^2 * (v x)^2 + 2 * (c x * v x * w x)) ∂μ) + (∫ x, (w x)^2 ∂μ) := by
        rw [integral_add ?_ hww]
        exact hvv.add (hvw.const_mul (2 : ℝ))
      _ = ((∫ x, (c x)^2 * (v x)^2 ∂μ) + (∫ x, 2 * (c x * v x * w x) ∂μ)) + (∫ x, (w x)^2 ∂μ) := by
        rw [integral_add hvv (hvw.const_mul (2 : ℝ))]
      _ = ((∫ x, (c x)^2 * (v x)^2 ∂μ) + 2 * (∫ x, c x * v x * w x ∂μ)) + (∫ x, (w x)^2 ∂μ) := by
        simp [integral_const_mul]
      _ = (∫ x, (c x)^2 * (v x)^2 ∂μ) + 2 * (∫ x, c x * v x * w x ∂μ) + (∫ x, (w x)^2 ∂μ) := by ring
  nlinarith

end EinsteinRelation.Correctors
