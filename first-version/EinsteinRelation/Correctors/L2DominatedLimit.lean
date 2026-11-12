import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory Filter
open scoped Topology ENNReal
namespace EinsteinRelation.Correctors

/-- Strong L² dominated convergence for an actual filter-indexed scalar family.
Source: `paper/main.tex:798–806`; differentiating temporal regularizations. -/
theorem tendsto_eLpNorm_two_of_dominated {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (l : Filter ι) [l.IsCountablyGenerated]
    {f : ι → Ω → ℝ} {b : Ω → ℝ}
    (hb : MemLp b 2 μ)
    (hf : ∀ᶠ i in l, AEStronglyMeasurable (f i) μ)
    (hbound : ∀ᶠ i in l, ∀ᵐ ω ∂μ, |f i ω| ≤ |b ω|)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun i => f i ω) l (𝓝 0)) :
    Tendsto (fun i => eLpNorm (f i) 2 μ) l (𝓝 0) := by
  have hi : Tendsto (fun i => ∫ ω, (f i ω)^2 ∂μ) l (𝓝 0) := by
    have ht := tendsto_integral_filter_of_dominated_convergence
      (fun ω => (b ω)^2)
      (hf.mono fun i hi => hi.pow 2)
      (hbound.mono fun i hi => hi.mono fun ω hω => by
        simpa only [Real.norm_eq_abs,Pi.pow_apply,abs_sq,sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hω 2)
      hb.integrable_sq
      (hlim.mono fun ω hω => by simpa using hω.pow 2)
    simpa using ht
  have hn : Tendsto (fun i => ENNReal.ofReal (Real.sqrt (∫ ω, (f i ω)^2 ∂μ)))
      l (𝓝 0) := by
    have hs : Tendsto (fun i => Real.sqrt (∫ ω, (f i ω)^2 ∂μ)) l (𝓝 0) := by
      simpa using (Real.continuous_sqrt.tendsto 0).comp hi
    simpa using (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hs
  apply hn.congr'
  filter_upwards [hf,hbound] with i hfi hbi
  have hmem : MemLp (f i) 2 μ := hb.mono hfi (hbi.mono fun ω hω => by
    simpa only [Real.norm_eq_abs] using hω)
  rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hmem]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
  rw [Real.sqrt_eq_rpow]
  simp only [one_div]


end EinsteinRelation.Correctors
