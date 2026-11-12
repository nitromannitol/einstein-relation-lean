import EinsteinRelation.Correctors.ProbabilityAverageL2
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors

/-- Time-only probability convolution contracts the actual space-time L²
norm. Source: `paper/main.tex:798–806`; temporal regularization. -/
theorem temporal_convolution_L2_contraction {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [SFinite ν] {u : ℝ × X → ℝ}
    (hu : MemLp u 2 (volume.prod ν))
    {ρ : ℝ → ℝ} (hρ : Continuous ρ) (hρc : HasCompactSupport ρ)
    (hρ0 : ∀ s, 0 ≤ ρ s) (hρ1 : (∫ s, ρ s) = 1) :
    MemLp (fun z : ℝ × X => ∫ s, ρ s * u (z.1-s,z.2)) 2 (volume.prod ν) ∧
      eLpNorm (fun z : ℝ × X => ∫ s, ρ s * u (z.1-s,z.2)) 2 (volume.prod ν) ≤
        eLpNorm u 2 (volume.prod ν) := by
  let μ : Measure ℝ := volume.withDensity (fun s => ENNReal.ofReal (ρ s))
  have hm := hρ.measurable.ennreal_ofReal
  have ht : ∀ᵐ s ∂(volume : Measure ℝ), ENNReal.ofReal (ρ s) < ∞ :=
    ae_of_all _ fun _ => ENNReal.ofReal_lt_top
  haveI : IsProbabilityMeasure μ := ⟨by
    dsimp only [μ]
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (hρ.integrable_of_hasCompactSupport hρc)
        (ae_of_all _ hρ0),hρ1,ENNReal.ofReal_one]⟩
  have hshift (s : ℝ) : MeasurePreserving
      (fun z : ℝ × X => (z.1-s,z.2)) (volume.prod ν) (volume.prod ν) :=
    (measurePreserving_sub_right volume s).prod (MeasurePreserving.id ν)
  have hskew := (MeasurePreserving.id μ).skew_product
    (g := fun s (z : ℝ × X) => (z.1-s,z.2))
    ((measurable_fst.comp measurable_snd |>.sub measurable_fst).prodMk
      (measurable_snd.comp measurable_snd))
    (ae_of_all _ fun s => (hshift s).map_eq)
  have hF : AEStronglyMeasurable
      (fun p : (ℝ × X) × ℝ => u (p.1.1-p.2,p.1.2)) ((volume.prod ν).prod μ) := by
    exact ((hu.1.comp_snd.comp_measurePreserving hskew).comp_measurePreserving
      (Measure.measurePreserving_swap (μ := volume.prod ν) (ν := μ)))
  have hb : ∀ᵐ s ∂μ, eLpNorm (fun z : ℝ × X => u (z.1-s,z.2)) 2 (volume.prod ν) ≤
      eLpNorm u 2 (volume.prod ν) := ae_of_all _ fun s =>
    (eLpNorm_comp_measurePreserving hu.1 (hshift s)).le
  have he := eLpNorm_probability_integral_le hF hb
  have heq (z : ℝ × X) : (∫ s, u (z.1-s,z.2) ∂μ) =
      ∫ s, ρ s * u (z.1-s,z.2) := by
    rw [show μ = volume.withDensity (fun s => ENNReal.ofReal (ρ s)) from rfl,
      integral_withDensity_eq_integral_toReal_smul hm ht]
    simp only [ENNReal.toReal_ofReal (hρ0 _),smul_eq_mul]
  have hmem : MemLp (fun z : ℝ × X => ∫ s, u (z.1-s,z.2) ∂μ) 2 (volume.prod ν) :=
    ⟨hF.integral_prod_right',he.trans_lt hu.2⟩
  simpa only [heq] using And.intro hmem he

end EinsteinRelation.Correctors
