import EinsteinRelation.Correctors.NormalizedSourceDominatedMoment
import EinsteinRelation.Correctors.IntegralMomentNormBound

/-! # Quantitative source norms under a dominating spatial measure

Source: `paper/main.tex:715–722,942–947`. Zero mollifier mean and centered
moments on ordinary normalized volume give an absolute source norm there.
-/

open MeasureTheory
namespace EinsteinRelation.Correctors

/-- A nested centered power bound controls the actual source on any dominating
probability measure. Source: `paper/main.tex:715–722,942–947`. -/
theorem memLp_normalized_source_of_dominated_centered_power_moment {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν γ : Measure X) [IsProbabilityMeasure ν] [IsProbabilityMeasure γ]
    {p B D : ℝ} (hp : 1 ≤ p) (hD : 0 ≤ D)
    (hdom : ν ≤ ENNReal.ofReal D • γ)
    (u : Ω → X → ℝ) (hum : StronglyMeasurable (Function.uncurry u))
    (c : Ω → ℝ) (hcm : StronglyMeasurable c)
    (hzero : ∀ᵐ ω ∂μ, (∫ x, u ω x ∂ν) = 0)
    (hb : (∫⁻ ω, ∫⁻ x, ENNReal.ofReal (|u ω x - c ω| ^ p) ∂γ ∂μ) ≤
      ENNReal.ofReal B) :
    MemLp (Function.uncurry u) (ENNReal.ofReal p) (μ.prod γ) ∧
      eLpNorm (Function.uncurry u) (ENNReal.ofReal p) (μ.prod γ) ≤
        ENNReal.ofReal ((1 + D ^ (1 / p)) * (max B 0) ^ (1 / p)) := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  let F : Ω × X → ℝ := fun z => u z.1 z.2 - c z.1
  have hFm : StronglyMeasurable F := hum.sub (hcm.comp_measurable measurable_fst)
  have hm : Measurable (fun z : Ω × X => ENNReal.ofReal (|F z| ^ p)) :=
    ((hFm.measurable.abs).pow_const p).ennreal_ofReal
  have hb' : (∫⁻ z : Ω × X, ENNReal.ofReal (|F z| ^ p) ∂μ.prod γ) ≤
      ENNReal.ofReal B := by simpa only [lintegral_prod _ hm.aemeasurable] using hb
  have hbn : eLpNorm F (ENNReal.ofReal p) (μ.prod γ) ≤
      ENNReal.ofReal ((max B 0) ^ (1 / p)) := by
    have hn := eLpNorm_le_of_lintegral_moment (μ.prod γ) hp0
      (fun z => abs_nonneg (F z)) hb'
    simpa only [← Real.norm_eq_abs, eLpNorm_norm] using hn
  have hFp : MemLp F (ENNReal.ofReal p) (μ.prod γ) :=
    ⟨hFm.aestronglyMeasurable, hbn.trans_lt ENNReal.ofReal_lt_top⟩
  obtain ⟨hmem, hnorm⟩ := memLp_normalized_source_of_dominated_centered_moment
    μ ν γ (ENNReal.one_le_ofReal.mpr hp) ENNReal.ofReal_ne_top
    ENNReal.ofReal_ne_top hdom u hum c hcm hzero hFp
  refine ⟨hmem, hnorm.trans ?_⟩
  have he : (1 / ENNReal.ofReal p).toReal = 1 / p := by
    simp only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofReal hp0.le]
  rw [he, ENNReal.ofReal_rpow_of_nonneg hD (one_div_nonneg.mpr hp0.le),
    ← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num) (Real.rpow_nonneg hD _)]
  calc
    _ ≤ ENNReal.ofReal (1 + D ^ (1 / p)) * ENNReal.ofReal ((max B 0) ^ (1 / p)) :=
      mul_le_mul_right hbn _
    _ = _ := (ENNReal.ofReal_mul (by positivity)).symm

end EinsteinRelation.Correctors
