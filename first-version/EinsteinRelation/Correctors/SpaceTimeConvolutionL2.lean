import EinsteinRelation.Correctors.ProbabilityAverageL2
import EinsteinRelation.Correctors.SpaceTimeTranslationL2
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.MeasureTheory.Group.Prod

/-! # Strong space-time L² convergence of compact regularizations

Source: `paper/main.tex:832–840`. Probability averaging bounds the
regularization error by small translation errors. Thus normalized compact
kernels approximate the actual energy-class field strongly in L².
-/

open MeasureTheory Filter Metric
open scoped Topology ENNReal Convolution

namespace EinsteinRelation.Correctors

/-- A compact probability kernel bounds its regularization error by the
L² translation error on its support. Source: `paper/main.tex:832–840`. -/
theorem paired_eLpNorm_convolution_sub_le {d : ℕ}
    {u ρ : ℝ × Vec d → ℝ} (hu : MemLp u 2 volume)
    (hρ : Continuous ρ) (hρc : HasCompactSupport ρ)
    (hρ0 : ∀ z, 0 ≤ ρ z) (hρ1 : (∫ z, ρ z) = 1)
    {B : ℝ≥0∞} (hB : ∀ w ∈ Function.support ρ,
      eLpNorm (fun z => u (z - w) - u z) 2 volume ≤ B) :
    eLpNorm (fun z => (∫ w, ρ w * u (z - w)) - u z) 2 volume ≤ B := by
  letI : (volume : Measure (ℝ × Vec d)).IsAddRightInvariant := by
    change ((volume : Measure ℝ).prod (volume : Measure (Vec d))).IsAddRightInvariant
    infer_instance
  letI : (volume : Measure (ℝ × Vec d)).IsAddLeftInvariant := by
    change ((volume : Measure ℝ).prod (volume : Measure (Vec d))).IsAddLeftInvariant
    infer_instance
  letI : (volume : Measure (ℝ × Vec d)).IsNegInvariant := by
    exact ⟨((Measure.measurePreserving_neg (volume : Measure ℝ)).prod
      (Measure.measurePreserving_neg (volume : Measure (Vec d)))).map_eq⟩
  let μ : Measure (ℝ × Vec d) := volume.withDensity (fun w => ENNReal.ofReal (ρ w))
  have hm : Measurable (fun w => ENNReal.ofReal (ρ w)) := hρ.measurable.ennreal_ofReal
  have ht : ∀ᵐ w ∂(volume : Measure (ℝ × Vec d)), ENNReal.ofReal (ρ w) < ∞ :=
    ae_of_all _ fun _ => ENNReal.ofReal_lt_top
  haveI : IsProbabilityMeasure μ := ⟨by
    dsimp only [μ]
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (hρ.integrable_of_hasCompactSupport hρc)
        (ae_of_all _ hρ0), hρ1, ENNReal.ofReal_one]⟩
  have hF : AEStronglyMeasurable (fun p : (ℝ × Vec d) × (ℝ × Vec d) =>
      u (p.1 - p.2) - u p.1) (volume.prod μ) :=
    (hu.1.comp_fst.comp_measurePreserving (measurePreserving_sub_prod volume μ)).sub
      hu.1.comp_fst
  have hs : ∀ᵐ w ∂μ, eLpNorm (fun z => u (z - w) - u z) 2 volume ≤ B := by
    apply (ae_withDensity_iff hm).mpr
    exact ae_of_all _ fun w hw => hB w (fun hz => hw (by simp only [hz, ENNReal.ofReal_zero]))
  have heq (z : ℝ × Vec d) : (∫ w, u (z - w) - u z ∂μ) =
      (∫ w, ρ w * u (z - w)) - u z := by
    have hi : Integrable (fun w => u (z - w)) μ := by
      apply (integrable_withDensity_iff_integrable_smul' hm ht).mpr
      simpa only [ENNReal.toReal_ofReal (hρ0 _), smul_eq_mul] using
        (hρc.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) hρ
          (hu.locallyIntegrable (by norm_num)) z)
    rw [integral_sub hi (integrable_const _), integral_const]
    simp only [probReal_univ, one_smul]
    rw [integral_withDensity_eq_integral_toReal_smul hm ht]
    simp only [ENNReal.toReal_ofReal (hρ0 _), smul_eq_mul]
  simpa only [heq] using eLpNorm_probability_integral_le hF hs

/-- Compact nonnegative unit-mass regularizations converge strongly in the
actual space-time L² seminorm. Source: `paper/main.tex:832–840`. -/
theorem paired_tendsto_convolution_L2 {d : ℕ}
    {u : ℝ × Vec d → ℝ} (hu : MemLp u 2 volume)
    {ρ : ℕ → ℝ × Vec d → ℝ}
    (hρ : ∀ k, Continuous (ρ k)) (hρc : ∀ k, HasCompactSupport (ρ k))
    (hρ0 : ∀ k z, 0 ≤ ρ k z) (hρ1 : ∀ k, (∫ z, ρ k z) = 1)
    {ε : ℕ → ℝ} (hεlim : Tendsto ε atTop (𝓝 0))
    (hρsupp : ∀ k, Function.support (ρ k) ⊆ closedBall 0 (ε k)) :
    Tendsto (fun k => eLpNorm
      (fun z => (∫ w, ρ k w * u (z - w)) - u z) 2 volume) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    exact (not_lt_of_ge (zero_le b) hb).elim
  · intro b hb
    obtain ⟨c, hc0, hcb⟩ := exists_between hb
    have hsmall := (paired_tendsto_spacetime_translate_L2 hu).eventually (gt_mem_nhds hc0)
    obtain ⟨δ, hδ, hδs⟩ := Metric.mem_nhds_iff.mp hsmall
    filter_upwards [hεlim.eventually (gt_mem_nhds hδ)] with k hk
    apply lt_of_le_of_lt (paired_eLpNorm_convolution_sub_le hu (hρ k) (hρc k)
      (hρ0 k) (hρ1 k) (fun w hw => ?_)) hcb
    have hwδ : -w ∈ ball (0 : ℝ × Vec d) δ := by
      rw [mem_ball_zero_iff, norm_neg]
      exact (mem_closedBall_zero_iff.mp (hρsupp k hw)).trans_lt hk
    simpa only [sub_eq_add_neg] using (hδs hwδ).le

/-- The same approximation in the order used by the weak energy tests.
Source: `paper/main.tex:832–840`. -/
theorem paired_tendsto_regularization_L2 {d : ℕ}
    {u : ℝ × Vec d → ℝ} (hu : MemLp u 2 volume)
    {ρ : ℕ → ℝ × Vec d → ℝ}
    (hρ : ∀ k, Continuous (ρ k)) (hρc : ∀ k, HasCompactSupport (ρ k))
    (hρ0 : ∀ k z, 0 ≤ ρ k z) (hρ1 : ∀ k, (∫ z, ρ k z) = 1)
    {ε : ℕ → ℝ} (hεlim : Tendsto ε atTop (𝓝 0))
    (hρsupp : ∀ k, Function.support (ρ k) ⊆ closedBall 0 (ε k)) :
    Tendsto (fun k => eLpNorm
      (fun z => (∫ w, u w * ρ k (z - w)) - u z) 2 volume) atTop (𝓝 0) := by
  letI : (volume : Measure (ℝ × Vec d)).IsAddLeftInvariant := by
    change ((volume : Measure ℝ).prod (volume : Measure (Vec d))).IsAddLeftInvariant
    infer_instance
  letI : (volume : Measure (ℝ × Vec d)).IsNegInvariant := by
    exact ⟨((Measure.measurePreserving_neg (volume : Measure ℝ)).prod
      (Measure.measurePreserving_neg (volume : Measure (Vec d)))).map_eq⟩
  have heq (k : ℕ) (z : ℝ × Vec d) :
      (∫ w, u w * ρ k (z - w)) = ∫ w, ρ k w * u (z - w) := by
    change (u ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] ρ k) z = _
    rw [convolution_mul_swap]
    simp only [mul_comm]
  simpa only [heq] using paired_tendsto_convolution_L2 hu hρ hρc hρ0 hρ1 hεlim hρsupp

end EinsteinRelation.Correctors
