import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas

open MeasureTheory
open scoped ENNReal

namespace EinsteinRelation.Correctors

/-- Source: paper/main.tex:842–852. A coupled difference is bounded by its
finite-time difference plus the two marginal tails, with no independence. -/
theorem eLpNorm_coupled_difference_le_approximation_add_tails
    {Ω Z E : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    [NormedAddCommGroup E] {μ : Measure Ω} {ν : Measure Z}
    {π₁ π₂ : Z → Ω} (h₁ : MeasurePreserving π₁ ν μ)
    (h₂ : MeasurePreserving π₂ ν μ) {p : ℝ≥0∞} (hp : 1 ≤ p)
    {f g : Ω → E} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) :
    eLpNorm (fun z => f (π₁ z) - f (π₂ z)) p ν ≤
      eLpNorm (fun z => g (π₁ z) - g (π₂ z)) p ν +
        2 * eLpNorm (f - g) p μ := by
  have h_diff : AEStronglyMeasurable (f - g) μ :=
    AEStronglyMeasurable.sub hf hg
  have h_comp₁ : AEStronglyMeasurable ((f - g) ∘ π₁) ν :=
    MeasureTheory.AEStronglyMeasurable.comp_measurePreserving h_diff h₁
  have h_comp₂ : AEStronglyMeasurable ((f - g) ∘ π₂) ν :=
    MeasureTheory.AEStronglyMeasurable.comp_measurePreserving h_diff h₂
  have h_g_comp₁ : AEStronglyMeasurable (g ∘ π₁) ν :=
    MeasureTheory.AEStronglyMeasurable.comp_measurePreserving hg h₁
  have h_g_comp₂ : AEStronglyMeasurable (g ∘ π₂) ν :=
    MeasureTheory.AEStronglyMeasurable.comp_measurePreserving hg h₂
  have h_g_diff : AEStronglyMeasurable (fun z => g (π₁ z) - g (π₂ z)) ν :=
    AEStronglyMeasurable.sub h_g_comp₁ h_g_comp₂
  have h_eq : (fun z => f (π₁ z) - f (π₂ z)) =
      (fun z => (((f - g) ∘ π₁) z - ((f - g) ∘ π₂) z) + (g (π₁ z) - g (π₂ z))) := by
    ext z
    dsimp
    abel
  rw [h_eq]
  have hA : AEStronglyMeasurable
      (fun z => (((f - g) ∘ π₁) z - ((f - g) ∘ π₂) z)) ν :=
    AEStronglyMeasurable.sub h_comp₁ h_comp₂
  have h_tri1 : eLpNorm (fun z => (((f - g) ∘ π₁) z - ((f - g) ∘ π₂) z) + (g (π₁ z) - g (π₂ z))) p ν ≤
      eLpNorm (fun z => (((f - g) ∘ π₁) z - ((f - g) ∘ π₂) z)) p ν +
      eLpNorm (fun z => g (π₁ z) - g (π₂ z)) p ν :=
    eLpNorm_add_le hA h_g_diff hp
  have h_tri2 : eLpNorm (fun z => (((f - g) ∘ π₁) z - ((f - g) ∘ π₂) z)) p ν ≤
      eLpNorm ((f - g) ∘ π₁) p ν + eLpNorm ((f - g) ∘ π₂) p ν :=
    eLpNorm_sub_le h_comp₁ h_comp₂ hp
  have h_norm₁ : eLpNorm ((f - g) ∘ π₁) p ν = eLpNorm (f - g) p μ :=
    eLpNorm_comp_measurePreserving h_diff h₁
  have h_norm₂ : eLpNorm ((f - g) ∘ π₂) p ν = eLpNorm (f - g) p μ :=
    eLpNorm_comp_measurePreserving h_diff h₂
  calc
    eLpNorm (fun z => (((f - g) ∘ π₁) z - ((f - g) ∘ π₂) z) + (g (π₁ z) - g (π₂ z))) p ν ≤
        eLpNorm (fun z => (((f - g) ∘ π₁) z - ((f - g) ∘ π₂) z)) p ν +
        eLpNorm (fun z => g (π₁ z) - g (π₂ z)) p ν := h_tri1
    _ ≤ (eLpNorm ((f - g) ∘ π₁) p ν + eLpNorm ((f - g) ∘ π₂) p ν) +
        eLpNorm (fun z => g (π₁ z) - g (π₂ z)) p ν := by
      gcongr
    _ = (eLpNorm (f - g) p μ + eLpNorm (f - g) p μ) +
        eLpNorm (fun z => g (π₁ z) - g (π₂ z)) p ν := by
      simp [h_norm₁, h_norm₂]
    _ = eLpNorm (fun z => g (π₁ z) - g (π₂ z)) p ν + (eLpNorm (f - g) p μ + eLpNorm (f - g) p μ) := by
      abel
    _ = eLpNorm (fun z => g (π₁ z) - g (π₂ z)) p ν + 2 * eLpNorm (f - g) p μ := by
      ring

end EinsteinRelation.Correctors
