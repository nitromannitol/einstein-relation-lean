import EinsteinRelation.Correctors.CoupledTailTriangle
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.Probability.Kernel.CondDistrib
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors

/-- Agreement of observations cancels the conditional mean in a coupling;
source `paper/main.tex:878–886`. -/
theorem coupled_difference_le_shared_observation_residual
    {Ω Z B : Type*} [MeasurableSpace Ω] [MeasurableSpace Z] [MeasurableSpace B]
    {d : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Z)
    (π₁ π₂ : Z → Ω) (h₁ : MeasurePreserving π₁ ν μ) (h₂ : MeasurePreserving π₂ ν μ)
    (X : Ω → B) (hX : Measurable X)
    (f : Ω → EuclideanSpace ℝ (Fin d)) (hfm : Measurable f) (hf : Integrable f μ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hshared : ∀ᵐ z ∂ν, X (π₁ z) = X (π₂ z)) :
    eLpNorm (fun z => f (π₁ z)-f (π₂ z)) p ν ≤
      2 * eLpNorm (f-μ[f | (inferInstance : MeasurableSpace B).comap X]) p μ := by
  set g := μ[f | (inferInstance : MeasurableSpace B).comap X] with hg_def
  have hg_stronglyMeasurable : StronglyMeasurable[(inferInstance : MeasurableSpace B).comap X] g :=
    stronglyMeasurable_condExp
  obtain ⟨h, hh_meas, hh_eq⟩ := hg_stronglyMeasurable.exists_eq_measurable_comp
  have h_agree : g ∘ π₁ =ᵐ[ν] g ∘ π₂ := by
    filter_upwards [hshared] with z hz
    calc
      g (π₁ z) = h (X (π₁ z)) := by rw [hh_eq]; rfl
      _ = h (X (π₂ z)) := by rw [hz]
      _ = g (π₂ z) := by rw [hh_eq]; rfl
  have h_diff_zero : g ∘ π₁ - g ∘ π₂ =ᵐ[ν] 0 := by
    filter_upwards [h_agree] with z hz
    change g (π₁ z) - g (π₂ z) = 0
    exact sub_eq_zero.mpr hz
  have hg_aestrongly : AEStronglyMeasurable g μ := by
    have : Integrable g μ := integrable_condExp
    exact this.aestronglyMeasurable
  have h_diff : AEStronglyMeasurable (f - g) μ :=
    AEStronglyMeasurable.sub hfm.aestronglyMeasurable hg_aestrongly
  have h_comp₁ : AEStronglyMeasurable ((f - g) ∘ π₁) ν :=
    MeasureTheory.AEStronglyMeasurable.comp_measurePreserving h_diff h₁
  have h_comp₂ : AEStronglyMeasurable ((f - g) ∘ π₂) ν :=
    MeasureTheory.AEStronglyMeasurable.comp_measurePreserving h_diff h₂
  have h_g_comp₁ : AEStronglyMeasurable (g ∘ π₁) ν :=
    MeasureTheory.AEStronglyMeasurable.comp_measurePreserving hg_aestrongly h₁
  have h_g_comp₂ : AEStronglyMeasurable (g ∘ π₂) ν :=
    MeasureTheory.AEStronglyMeasurable.comp_measurePreserving hg_aestrongly h₂
  have h_g_diff : AEStronglyMeasurable (g ∘ π₁ - g ∘ π₂) ν :=
    AEStronglyMeasurable.sub h_g_comp₁ h_g_comp₂
  have h_eq : (fun z => f (π₁ z) - f (π₂ z)) =
      (fun z => (((f - g) ∘ π₁) z - ((f - g) ∘ π₂) z) + ((g ∘ π₁ - g ∘ π₂) z)) := by
    ext z
    dsimp
    abel
  rw [h_eq]
  have hA : AEStronglyMeasurable
      (fun z => (((f - g) ∘ π₁) z - ((f - g) ∘ π₂) z)) ν :=
    AEStronglyMeasurable.sub h_comp₁ h_comp₂
  have h_tri1 : eLpNorm (fun z => (((f - g) ∘ π₁) z - ((f - g) ∘ π₂) z) + ((g ∘ π₁ - g ∘ π₂) z)) p ν ≤
      eLpNorm (fun z => (((f - g) ∘ π₁) z - ((f - g) ∘ π₂) z)) p ν +
      eLpNorm (g ∘ π₁ - g ∘ π₂) p ν :=
    eLpNorm_add_le hA h_g_diff hp
  have h_tri2 : eLpNorm (fun z => (((f - g) ∘ π₁) z - ((f - g) ∘ π₂) z)) p ν ≤
      eLpNorm ((f - g) ∘ π₁) p ν + eLpNorm ((f - g) ∘ π₂) p ν :=
    eLpNorm_sub_le h_comp₁ h_comp₂ hp
  have h_norm₁ : eLpNorm ((f - g) ∘ π₁) p ν = eLpNorm (f - g) p μ :=
    eLpNorm_comp_measurePreserving h_diff h₁
  have h_norm₂ : eLpNorm ((f - g) ∘ π₂) p ν = eLpNorm (f - g) p μ :=
    eLpNorm_comp_measurePreserving h_diff h₂
  have h_mid_zero : eLpNorm (g ∘ π₁ - g ∘ π₂) p ν = 0 := by
    rw [eLpNorm_congr_ae h_diff_zero, eLpNorm_zero]
  calc
    eLpNorm (fun z => (((f - g) ∘ π₁) z - ((f - g) ∘ π₂) z) + ((g ∘ π₁ - g ∘ π₂) z)) p ν ≤
        eLpNorm (fun z => (((f - g) ∘ π₁) z - ((f - g) ∘ π₂) z)) p ν +
        eLpNorm (g ∘ π₁ - g ∘ π₂) p ν := h_tri1
    _ ≤ (eLpNorm ((f - g) ∘ π₁) p ν + eLpNorm ((f - g) ∘ π₂) p ν) +
        eLpNorm (g ∘ π₁ - g ∘ π₂) p ν := by
      gcongr
    _ = (eLpNorm (f - g) p μ + eLpNorm (f - g) p μ) + 0 := by
      simp [h_norm₁, h_norm₂, h_mid_zero]
    _ = eLpNorm (f - g) p μ + eLpNorm (f - g) p μ := by simp
    _ = 2 * eLpNorm (f - g) p μ := by ring
    _ = 2 * eLpNorm (f - μ[f | (inferInstance : MeasurableSpace B).comap X]) p μ := by rfl
end EinsteinRelation.Correctors
