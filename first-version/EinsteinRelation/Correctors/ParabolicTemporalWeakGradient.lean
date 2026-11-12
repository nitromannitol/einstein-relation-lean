import EinsteinRelation.Correctors.WeightedWeakGradientAveraging
import EinsteinRelation.Correctors.PairedPDECutoffEnergyClass

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Temporal averaging of an actual energy-class solution preserves its actual
spatial weak gradient. Source: `paper/main.tex:798–806`; temporal smoothing. -/
theorem parabolicSolution_temporal_weakGradient {d : ℕ} {K a b : ℝ}
    {A : Coefficient d K} {U : Set (Vec d)}
    [IsFiniteMeasure (volume.restrict U)]
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsParabolicSolution A (Set.Ioo a b) U u G)
    {ρ : ℝ → ℝ} (hρ : Continuous ρ) (hρc : HasCompactSupport ρ) :
    HasWeakGradient U
      (fun x => ∫ s in Set.Ioo a b, ρ s * u (s,x))
      (fun x j => ∫ s in Set.Ioo a b, ρ s * G (s,x) j) := by
  let μ := volume.restrict (Set.Ioo a b)
  let ν := volume.restrict U
  have hp : volume.restrict (Set.Ioo a b ×ˢ U) = μ.prod ν := by
    simp only [μ,ν,Measure.volume_eq_prod,Measure.prod_restrict]
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioo a b ×ˢ U)) := by
    rw [hp]
    infer_instance
  have hmul {f : ℝ × Vec d → ℝ}
      (hf : MemLp f 2 (volume.restrict (Set.Ioo a b ×ˢ U))) :
      Integrable (fun z : ℝ × Vec d => ρ z.1 * f z) (μ.prod ν) := by
    obtain ⟨C,hC⟩ := hρc.exists_bound_of_continuous hρ
    rw [← hp]
    simpa only [mul_comm,Function.comp_apply] using (hf.integrable (by norm_num)).mul_bdd
      ((hρ.measurable.comp measurable_fst).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun z => hC z.1)
  exact hasWeakGradient_signed_weighted_integral μ U ρ (fun s x => u (s,x))
    (fun s x => G (s,x)) (hmul hsol.1)
    (fun j => hmul (parabolicSolution_gradient_coordinate_memLp hsol j)) hsol.2.2.2.1

end EinsteinRelation.Correctors
