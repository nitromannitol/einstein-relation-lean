import EinsteinRelation.Correctors.TimeIntegralLpBound

/-! # Vector-valued time Minkowski bounds

Source: `paper/main.tex:800–808`. The original positive-majorant estimate
is extended to almost every time, preserving the literal integral.
-/

open MeasureTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors

/-- Probability Minkowski for a Bochner-valued time integral.
Source: `paper/main.tex:800–808`. -/
theorem eLpNorm_vector_integral_le_integral_bound
    {Ω T E : Type*} [MeasurableSpace Ω] [MeasurableSpace T]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure Ω) [SFinite μ] (ν : Measure T) [SFinite ν]
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    (f : Ω × T → E) (hf : StronglyMeasurable f)
    {B : T → ℝ} (hB : Measurable B) (hBi : Integrable B ν)
    (hBpos : ∀ t, 0 < B t) (hmass : 0 < ∫ t, B t ∂ν)
    (hbound : ∀ t, eLpNorm (fun ω => f (ω,t)) p μ ≤ ENNReal.ofReal (B t)) :
    eLpNorm (fun ω => ∫ t, f (ω,t) ∂ν) p μ ≤
      ENNReal.ofReal (∫ t, B t ∂ν) := by
  let g : Ω × T → ℝ := fun p => ‖f p‖
  have hg : StronglyMeasurable g := by
    simpa [g] using hf.norm
  have hgbound : ∀ t, eLpNorm (fun ω => g (ω, t)) p μ ≤ ENNReal.ofReal (B t) := by
    intro t
    dsimp [g]
    rw [eLpNorm_norm]
    exact hbound t
  have h_scalar := eLpNorm_integral_le_integral_bound ν hp hpt hg.measurable hB hBi hBpos hmass hgbound
  have h_pointwise : ∀ ω, ‖(∫ t, f (ω, t) ∂ν)‖ₑ ≤ ‖(∫ t, g (ω, t) ∂ν)‖ₑ := by
    intro ω
    have h := norm_integral_le_integral_norm (μ := ν) (fun t => f (ω, t))
    have h_nonneg : 0 ≤ ∫ t, g (ω, t) ∂ν := by
      refine integral_nonneg (fun t => ?_)
      dsimp [g]
      exact norm_nonneg _
    calc
      ‖(∫ t, f (ω, t) ∂ν)‖ₑ = ENNReal.ofReal ‖(∫ t, f (ω, t) ∂ν)‖ := by
        rw [← ofReal_norm_eq_enorm]
      _ ≤ ENNReal.ofReal (∫ t, ‖f (ω, t)‖ ∂ν) :=
        ENNReal.ofReal_le_ofReal h
      _ = ENNReal.ofReal ‖(∫ t, g (ω, t) ∂ν)‖ := by
        rw [show (∫ t, g (ω, t) ∂ν) = (∫ t, ‖f (ω, t)‖ ∂ν) by simp [g],
          Real.norm_of_nonneg h_nonneg]
      _ = ‖(∫ t, g (ω, t) ∂ν)‖ₑ := by rw [ofReal_norm_eq_enorm]
  have h_result := eLpNorm_mono_enorm (μ := μ) (p := p) h_pointwise
  exact h_result.trans h_scalar

/-- A time-null exceptional set in the moment bound does not affect the
literal Bochner integral. Source: `paper/main.tex:800–808`. -/
theorem eLpNorm_vector_integral_le_integral_bound_ae
    {Ω T E : Type*} [MeasurableSpace Ω] [MeasurableSpace T]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure Ω) [SFinite μ] (ν : Measure T) [SFinite ν]
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    (f : Ω × T → E) (hf : StronglyMeasurable f)
    {B : T → ℝ} (hB : Measurable B) (hBi : Integrable B ν)
    (hBpos : ∀ t, 0 < B t) (hmass : 0 < ∫ t, B t ∂ν)
    (hbound : ∀ᵐ t ∂ν, eLpNorm (fun ω => f (ω,t)) p μ ≤ ENNReal.ofReal (B t)) :
    eLpNorm (fun ω => ∫ t, f (ω,t) ∂ν) p μ ≤
      ENNReal.ofReal (∫ t, B t ∂ν) := by
  obtain ⟨N,hNsub,hNm,hNzero⟩ := exists_measurable_superset_of_null (ae_iff.mp hbound)
  let g : Ω × T → E := (Prod.snd ⁻¹' Nᶜ).indicator f
  have hg : StronglyMeasurable g := hf.indicator (hNm.compl.preimage measurable_snd)
  have hgb (t : T) : eLpNorm (fun ω => g (ω,t)) p μ ≤ ENNReal.ofReal (B t) := by
    by_cases ht : t ∈ N
    · have heq : (fun ω => g (ω,t)) = 0 := by funext ω; simp [g,ht]
      rw [heq,eLpNorm_zero]
      exact bot_le
    · have hb : eLpNorm (fun ω => f (ω,t)) p μ ≤ ENNReal.ofReal (B t) := by
        by_contra h
        exact ht (hNsub h)
      have heq : (fun ω => g (ω,t)) = fun ω => f (ω,t) := by
        funext ω
        exact Set.indicator_of_mem (show (ω,t) ∈ Prod.snd ⁻¹' Nᶜ from ht) f
      simpa only [heq] using hb
  have hNa : ∀ᵐ t ∂ν, t ∉ N := by simpa [ae_iff] using hNzero
  have heq (ω : Ω) : (∫ t, g (ω,t) ∂ν) = ∫ t, f (ω,t) ∂ν := by
    apply integral_congr_ae
    filter_upwards [hNa] with t ht
    exact Set.indicator_of_mem (show (ω,t) ∈ Prod.snd ⁻¹' Nᶜ from ht) f
  simpa only [heq] using eLpNorm_vector_integral_le_integral_bound μ ν hp hpt
    g hg hB hBi hBpos hmass hgb

end EinsteinRelation.Correctors
