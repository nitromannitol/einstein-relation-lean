import EinsteinRelation.Correctors.IntegralMoment

/-! # Moment estimates for vector and matrix averages

Source: `paper/main.tex:926–967`, the averaging steps in Proposition 5.3.
The scalar Minkowski estimate is applied to the norm of the field, preserving
the chosen norm on its value space. In particular, using a Euclidean value space
does not incur a coordinate or dimension factor.
-/

open MeasureTheory
open scoped ENNReal

namespace EinsteinRelation.Correctors

/-- Minkowski's estimate for sample integrals with values in a normed space.
Source: `paper/main.tex:926–967`. The majorant is integrable in the averaging
variable; no independence or stationarity is required. -/
theorem normed_integral_moment_le {Ω X E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (ν : Measure X) [SigmaFinite ν]
    {p : ℝ} (hp : 1 ≤ p) (H : X → ℝ) (hHm : Measurable H)
    (hH : ∀ x, 0 ≤ H x) (hHi : Integrable H ν)
    (f : X × Ω → E) (hf : Measurable f)
    (hmem : ∀ x, MemLp (fun ω => f (x, ω)) (ENNReal.ofReal p) Q ∧
      eLpNorm (fun ω => f (x, ω)) (ENNReal.ofReal p) Q ≤ ENNReal.ofReal (H x)) :
    (∀ᵐ ω ∂Q, Integrable (fun x => f (x, ω)) ν) ∧
      MemLp (fun ω => ∫ x, f (x, ω) ∂ν) (ENNReal.ofReal p) Q ∧
      eLpNorm (fun ω => ∫ x, f (x, ω) ∂ν) (ENNReal.ofReal p) Q ≤
        ENNReal.ofReal (∫ x, H x ∂ν) := by
  obtain ⟨hsec, hnorm, hbound⟩ := integral_moment_le Q ν hp H hHm hH hHi
    (fun z => ‖f z‖) hf.norm (fun x => by
      have hmx : AEStronglyMeasurable (fun ω => f (x, ω)) Q := (hmem x).1.aestronglyMeasurable
      have e : eLpNorm (fun ω => ‖f (x, ω)‖) (ENNReal.ofReal p) Q =
          eLpNorm (fun ω => f (x, ω)) (ENNReal.ofReal p) Q := eLpNorm_norm _ hmx
      exact ⟨(hmem x).1.norm, e.trans_le (hmem x).2⟩)
  have hfi : ∀ᵐ ω ∂Q, Integrable (fun x => f (x, ω)) ν := by
    filter_upwards [hsec] with ω hω
    exact (integrable_norm_iff
      (hf.comp measurable_prodMk_right).aestronglyMeasurable).mp hω
  have hsm : StronglyMeasurable (fun ω => ∫ x, f (x, ω) ∂ν) :=
    (hf.comp measurable_swap).stronglyMeasurable.integral_prod_right'
  have hle : ∀ᵐ ω ∂Q, ‖∫ x, f (x, ω) ∂ν‖ ≤ ‖∫ x, ‖f (x, ω)‖ ∂ν‖ :=
    Filter.Eventually.of_forall fun ω => (norm_integral_le_integral_norm _).trans
      (le_abs_self _)
  exact ⟨hfi, hnorm.of_le hsm.aestronglyMeasurable hle,
    (eLpNorm_mono_ae hsm.aestronglyMeasurable hle).trans hbound⟩

end EinsteinRelation.Correctors
