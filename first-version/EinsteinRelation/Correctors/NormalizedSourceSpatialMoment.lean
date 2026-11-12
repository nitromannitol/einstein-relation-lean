import EinsteinRelation.Correctors.KernelLpContraction
import Mathlib.MeasureTheory.Integral.Prod

/-! # Recovering normalized source moments from centered moments

Source: `paper/main.tex:913–925,942–947`. A zero mollifier mean controls
the absolute source moment by twice its moment relative to any spatially
constant random centering. All normalization identities hold almost surely.
-/

open MeasureTheory
open scoped ENNReal

namespace EinsteinRelation.Correctors

/-- A spatially normalized source has product-space moment at most twice
its moment about an arbitrary measurable random constant.
Source: `paper/main.tex:913–925,942–947`. -/
theorem memLp_normalized_source_of_centered_moment {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure X) [IsProbabilityMeasure ν]
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    (u : Ω → X → ℝ) (hum : StronglyMeasurable (Function.uncurry u))
    (c : Ω → ℝ) (hcm : StronglyMeasurable c)
    (hzero : ∀ᵐ ω ∂μ, (∫ x, u ω x ∂ν) = 0)
    (hcenter : MemLp (fun z : Ω × X => u z.1 z.2 - c z.1) p (μ.prod ν)) :
    MemLp (Function.uncurry u) p (μ.prod ν) ∧
      eLpNorm (Function.uncurry u) p (μ.prod ν) ≤
        2 * eLpNorm (fun z : Ω × X => u z.1 z.2 - c z.1) p (μ.prod ν) := by
  let F : Ω × X → ℝ := fun z => u z.1 z.2 - c z.1
  have hFm : StronglyMeasurable F := hum.sub (hcm.comp_measurable measurable_fst)
  let a : Ω → ℝ := fun ω => ∫ x, F (ω,x) ∂ν
  have ham : StronglyMeasurable a := hFm.integral_prod_right'
  have hab : eLpNorm a p μ ≤ eLpNorm F p (μ.prod ν) := by
    simpa only [ProbabilityTheory.Kernel.const_apply, Measure.compProd_const] using
      eLpNorm_kernel_integral_le (μ := μ) (ProbabilityTheory.Kernel.const Ω ν) hp hpt hFm
  have hap : MemLp a p μ :=
    ⟨ham.aestronglyMeasurable, hab.trans_lt hcenter.eLpNorm_lt_top⟩
  have hfst : MeasurePreserving (Prod.fst : Ω × X → Ω) (μ.prod ν) μ :=
    measurePreserving_fst
  have halift := hap.comp_measurePreserving hfst
  have hae : (fun z : Ω × X => F z - a z.1) =ᵐ[μ.prod ν] Function.uncurry u := by
    have hsec : ∀ᵐ ω ∂μ, (∫ x, F (ω,x) ∂ν) = -c ω := by
      filter_upwards [(hcenter.integrable hp).prod_right_ae, hzero] with ω hω hz
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
    _ ≤ eLpNorm F p (μ.prod ν) + eLpNorm (a ∘ Prod.fst) p (μ.prod ν) :=
      eLpNorm_sub_le hcenter.aestronglyMeasurable halift.aestronglyMeasurable hp
    _ = eLpNorm F p (μ.prod ν) + eLpNorm a p μ := by
      rw [eLpNorm_comp_measurePreserving ham.aestronglyMeasurable hfst]
    _ ≤ 2 * eLpNorm F p (μ.prod ν) := by
      simpa only [two_mul] using add_le_add_right hab (eLpNorm F p (μ.prod ν))

end EinsteinRelation.Correctors
