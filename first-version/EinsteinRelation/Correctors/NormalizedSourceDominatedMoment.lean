import EinsteinRelation.Correctors.NormalizedSourceSpatialMoment
import Mathlib.MeasureTheory.Measure.WithDensity

/-! # Transfer normalization between spatial measures

Source: `paper/main.tex:913–925,942–947`. A source normalized by one
probability measure inherits centered moments measured by any probability
measure that dominates the normalizing measure with bounded density.
This permits ordinary spatial integrability on larger balls.
-/

open MeasureTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors

/-- Centered spatial moments on a dominating probability measure control
an actual normalized source on that measure.
Source: `paper/main.tex:913–925,942–947`. -/
theorem memLp_normalized_source_of_dominated_centered_moment {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν γ : Measure X) [IsProbabilityMeasure ν] [IsProbabilityMeasure γ]
    {p K : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞) (hK : K ≠ ∞)
    (hdom : ν ≤ K • γ)
    (u : Ω → X → ℝ) (hum : StronglyMeasurable (Function.uncurry u))
    (c : Ω → ℝ) (hcm : StronglyMeasurable c)
    (hzero : ∀ᵐ ω ∂μ, (∫ x, u ω x ∂ν) = 0)
    (hcenter : MemLp (fun z : Ω × X => u z.1 z.2 - c z.1) p (μ.prod γ)) :
    MemLp (Function.uncurry u) p (μ.prod γ) ∧
      eLpNorm (Function.uncurry u) p (μ.prod γ) ≤
        (1 + K ^ (1 / p).toReal) *
          eLpNorm (fun z : Ω × X => u z.1 z.2 - c z.1) p (μ.prod γ) := by
  let F : Ω × X → ℝ := fun z => u z.1 z.2 - c z.1
  have hFm : StronglyMeasurable F := hum.sub (hcm.comp_measurable measurable_fst)
  have hprod : μ.prod ν ≤ K • (μ.prod γ) := by
    rw [← Measure.prod_smul_right]
    apply Measure.le_iff.mpr
    intro s hs
    rw [Measure.prod_apply hs, Measure.prod_apply hs]
    exact lintegral_mono fun ω => hdom (Prod.mk ω ⁻¹' s)
  have hFν : MemLp F p (μ.prod ν) := hcenter.of_measure_le_smul hK hprod
  have hnormν : eLpNorm F p (μ.prod ν) ≤
      K ^ (1 / p).toReal * eLpNorm F p (μ.prod γ) := by
    calc
      _ ≤ eLpNorm F p (K • (μ.prod γ)) := eLpNorm_mono_measure F hprod
      _ = _ := by rw [eLpNorm_smul_measure_of_ne_top hpt, smul_eq_mul]
  let a : Ω → ℝ := fun ω => ∫ x, F (ω,x) ∂ν
  have ham : StronglyMeasurable a := hFm.integral_prod_right'
  have hab : eLpNorm a p μ ≤ eLpNorm F p (μ.prod ν) := by
    simpa only [ProbabilityTheory.Kernel.const_apply, Measure.compProd_const] using
      eLpNorm_kernel_integral_le (μ := μ) (ProbabilityTheory.Kernel.const Ω ν) hp hpt hFm
  have hap : MemLp a p μ :=
    ⟨ham.aestronglyMeasurable, hab.trans_lt hFν.eLpNorm_lt_top⟩
  have hfst : MeasurePreserving (Prod.fst : Ω × X → Ω) (μ.prod γ) μ :=
    measurePreserving_fst
  have halift := hap.comp_measurePreserving hfst
  have hae : (fun z : Ω × X => F z - a z.1) =ᵐ[μ.prod γ] Function.uncurry u := by
    have hsec : ∀ᵐ ω ∂μ, (∫ x, F (ω,x) ∂ν) = -c ω := by
      filter_upwards [(hFν.integrable hp).prod_right_ae, hzero] with ω hω hz
      have hui : Integrable (u ω) ν := by
        have hsum : Integrable (fun x => (u ω x - c ω) + c ω) ν :=
          hω.add (integrable_const (c ω))
        simpa only [sub_add_cancel] using hsum
      dsimp only [F]
      rw [integral_sub hui (integrable_const _), hz, integral_const,
        probReal_univ, one_smul, zero_sub]
    filter_upwards [hfst.quasiMeasurePreserving.ae hsec] with z hz
    dsimp only [F, a, Function.uncurry]
    rw [hz]
    ring
  refine ⟨MemLp.ae_eq hae (hcenter.sub halift), ?_⟩
  rw [← eLpNorm_congr_ae hae]
  calc
    _ ≤ eLpNorm F p (μ.prod γ) + eLpNorm (a ∘ Prod.fst) p (μ.prod γ) :=
      eLpNorm_sub_le hcenter.aestronglyMeasurable halift.aestronglyMeasurable hp
    _ = eLpNorm F p (μ.prod γ) + eLpNorm a p μ := by
      rw [eLpNorm_comp_measurePreserving ham.aestronglyMeasurable hfst]
    _ ≤ eLpNorm F p (μ.prod γ) + K ^ (1 / p).toReal * eLpNorm F p (μ.prod γ) :=
      add_le_add le_rfl (hab.trans hnormν)
    _ = _ := by rw [add_mul, one_mul]

end EinsteinRelation.Correctors
