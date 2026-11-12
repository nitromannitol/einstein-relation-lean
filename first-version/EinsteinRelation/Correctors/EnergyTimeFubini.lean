import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Algebra.Support

/-! # Time testing spatial energy integrals

Source: `paper/main.tex:824–832`. Genuine cylinder integrability justifies
Fubini for compact temporal multipliers of the energy and its flux.
-/
open MeasureTheory
namespace EinsteinRelation.Correctors

/-- A compact continuous temporal multiplier can be moved through the
spatial integral of an integrable cylinder field.
Source: `paper/main.tex:824–832`. -/
theorem integral_time_mul_spatial_integral {X : Type*} [MeasurableSpace X]
    (μ : Measure ℝ) [SFinite μ] (ν : Measure X) [SFinite ν]
    {F : ℝ × X → ℝ} (hF : Integrable F (μ.prod ν))
    {η : ℝ → ℝ} (hη : Continuous η) (hηc : HasCompactSupport η) :
    (∫ z, η z.1 * F z ∂μ.prod ν) = ∫ t, η t * (∫ x, F (t,x) ∂ν) ∂μ := by
  obtain ⟨B, hB⟩ := hηc.exists_bound_of_continuous hη
  have hi : Integrable (fun z : ℝ × X => η z.1 * F z) (μ.prod ν) :=
    hF.bdd_mul (hη.measurable.comp measurable_fst).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => hB z.1)
  rw [integral_prod _ hi]
  simp only [integral_const_mul]

end EinsteinRelation.Correctors
