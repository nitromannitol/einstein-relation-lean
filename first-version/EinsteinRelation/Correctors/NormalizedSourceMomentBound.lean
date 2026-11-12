import EinsteinRelation.Correctors.NormalizedSourceSpatialMoment
import EinsteinRelation.Correctors.IntegralMomentNormBound

/-! # Absolute source norms from normalized centered moments

Source: `paper/main.tex:715–722,913–925,942–947`. The almost-sure spatial
normalization converts a centered power-moment estimate into an absolute
product-space norm bound.
-/

open MeasureTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors

/-- A literal normalized source has controlled absolute product norm once
its centered power moment is bounded. Source: `paper/main.tex:715–722,942–947`. -/
theorem memLp_normalized_source_of_centered_power_moment {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure X) [IsProbabilityMeasure ν]
    {p B : ℝ} (hp : 1 ≤ p)
    (u : Ω → X → ℝ) (hum : StronglyMeasurable (Function.uncurry u))
    (c : Ω → ℝ) (hcm : StronglyMeasurable c)
    (hzero : ∀ᵐ ω ∂μ, (∫ x, u ω x ∂ν) = 0)
    (hb : (∫⁻ z : Ω × X, ENNReal.ofReal (|u z.1 z.2 - c z.1| ^ p)
      ∂μ.prod ν) ≤ ENNReal.ofReal B) :
    MemLp (Function.uncurry u) (ENNReal.ofReal p) (μ.prod ν) ∧
      eLpNorm (Function.uncurry u) (ENNReal.ofReal p) (μ.prod ν) ≤
        ENNReal.ofReal (2 * (max B 0) ^ (1 / p)) := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  let F : Ω × X → ℝ := fun z => u z.1 z.2 - c z.1
  have hFm : StronglyMeasurable F := hum.sub (hcm.comp_measurable measurable_fst)
  have hbn : eLpNorm F (ENNReal.ofReal p) (μ.prod ν) ≤
      ENNReal.ofReal ((max B 0) ^ (1 / p)) := by
    have hn := eLpNorm_le_of_lintegral_moment (μ.prod ν) hp0
      (fun z => abs_nonneg (F z)) hb
    simpa only [← Real.norm_eq_abs, eLpNorm_norm] using hn
  have hFp : MemLp F (ENNReal.ofReal p) (μ.prod ν) :=
    ⟨hFm.aestronglyMeasurable, hbn.trans_lt ENNReal.ofReal_lt_top⟩
  obtain ⟨hmem, hnorm⟩ := memLp_normalized_source_of_centered_moment
    μ ν (ENNReal.one_le_ofReal.mpr hp) ENNReal.ofReal_ne_top u hum c hcm hzero hFp
  refine ⟨hmem, hnorm.trans ?_⟩
  calc
    _ ≤ 2 * ENNReal.ofReal ((max B 0) ^ (1 / p)) := mul_le_mul_right hbn 2
    _ = _ := by rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]; norm_num


/-- The nested form of the centered power estimate has the same absolute
source consequence. Source: `paper/main.tex:715–722,942–947`. -/
theorem memLp_normalized_source_of_nested_centered_power_moment {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure X) [IsProbabilityMeasure ν]
    {p B : ℝ} (hp : 1 ≤ p)
    (u : Ω → X → ℝ) (hum : StronglyMeasurable (Function.uncurry u))
    (c : Ω → ℝ) (hcm : StronglyMeasurable c)
    (hzero : ∀ᵐ ω ∂μ, (∫ x, u ω x ∂ν) = 0)
    (hb : (∫⁻ ω, ∫⁻ x, ENNReal.ofReal (|u ω x - c ω| ^ p) ∂ν ∂μ) ≤
      ENNReal.ofReal B) :
    MemLp (Function.uncurry u) (ENNReal.ofReal p) (μ.prod ν) ∧
      eLpNorm (Function.uncurry u) (ENNReal.ofReal p) (μ.prod ν) ≤
        ENNReal.ofReal (2 * (max B 0) ^ (1 / p)) := by
  apply memLp_normalized_source_of_centered_power_moment μ ν hp u hum c hcm hzero
  have hm : Measurable (fun z : Ω × X => ENNReal.ofReal (|u z.1 z.2 - c z.1| ^ p)) :=
    (((hum.measurable.sub (hcm.measurable.comp measurable_fst)).abs).pow_const p).ennreal_ofReal
  simpa only [lintegral_prod _ hm.aemeasurable] using hb

end EinsteinRelation.Correctors
