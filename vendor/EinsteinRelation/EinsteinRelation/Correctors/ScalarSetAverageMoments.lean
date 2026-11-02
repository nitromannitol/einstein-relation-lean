import EinsteinRelation.Correctors.ScalarMomentAverage
import Mathlib.MeasureTheory.Integral.Average

/-! # Scalar moments on finite space-time domains

Source: `paper/main.tex:834–845`. Normalized finite-volume averages inherit
pointwise probability moments on the averaging domain. No bound outside
that domain is required.
-/

open MeasureTheory
open scoped ENNReal

namespace EinsteinRelation.Correctors

/-- The actual normalized L² average on a positive finite-measure domain
inherits uniform scalar probability moments. Source: `paper/main.tex:834–845`. -/
theorem scalarL2_setAverage_moment_le {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] (Q : Measure Ω) [IsProbabilityMeasure Q] (μ : Measure X)
    {D : Set X} (hD : MeasurableSet D) (hD0 : μ D ≠ 0) (hDfin : μ D ≠ ∞)
    {p C : ℝ} (hp : 2 ≤ p) (hC : 0 ≤ C) (f : Ω × X → ℝ) (hf : Measurable f)
    (hmom : ∀ x ∈ D, MemLp (fun ω => f (ω, x)) (ENNReal.ofReal p) Q ∧
      eLpNorm (fun ω => f (ω, x)) (ENNReal.ofReal p) Q ≤ ENNReal.ofReal C) :
    MemLp (fun ω => Real.sqrt (⨍ x in D, f (ω, x) ^ 2 ∂μ)) (ENNReal.ofReal p) Q ∧
      eLpNorm (fun ω => Real.sqrt (⨍ x in D, f (ω, x) ^ 2 ∂μ))
        (ENNReal.ofReal p) Q ≤ ENNReal.ofReal C := by
  let ν := (μ D)⁻¹ • μ.restrict D
  letI : IsProbabilityMeasure ν := ⟨by
    simp only [ν, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ]
    exact ENNReal.inv_mul_cancel hD0 hDfin⟩
  let g : Ω × X → ℝ := (Prod.snd ⁻¹' D).indicator f
  have hgm : Measurable g := hf.indicator (hD.preimage measurable_snd)
  have hgmom (x : X) : MemLp (fun ω => g (ω, x)) (ENNReal.ofReal p) Q ∧
      eLpNorm (fun ω => g (ω, x)) (ENNReal.ofReal p) Q ≤ ENNReal.ofReal C := by
    by_cases hx : x ∈ D
    · simpa only [g, Set.indicator_of_mem, Set.mem_preimage, hx] using hmom x hx
    · simp only [g, Set.indicator_of_notMem, Set.mem_preimage, hx, not_false_eq_true]
      exact ⟨MemLp.zero, by simp⟩
  have h := (scalarL2_average_moment_le Q ν hp hC g hgm hgmom).2
  have heq (ω : Ω) : (∫ x, g (ω, x)^2 ∂ν) = ⨍ x in D, f (ω, x)^2 ∂μ := by
    rw [setAverage_eq']
    apply integral_congr_ae
    apply Measure.ae_smul_measure _ (μ D)⁻¹
    filter_upwards [ae_restrict_mem hD] with x hx
    simp only [g, Set.indicator_of_mem (show (ω, x) ∈ Prod.snd ⁻¹' D from hx)]
  simpa only [heq] using h

end EinsteinRelation.Correctors
