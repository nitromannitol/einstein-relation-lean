import EinsteinRelation.Correctors.ParabolicTemporalWeakGradient
import EinsteinRelation.Correctors.CoordinatePairingIntegrals

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Temporal averaging commutes with the actual spatial coefficient field.
Source: `paper/main.tex:798–806`. -/
theorem parabolicSolution_temporal_flux_commute {d : ℕ} {K a b : ℝ}
    {A : Coefficient d K} {U : Set (Vec d)}
    [IsFiniteMeasure (volume.restrict U)]
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsParabolicSolution A (Set.Ioo a b) U u G)
    {ρ : ℝ → ℝ} (hρ : Continuous ρ) (hρc : HasCompactSupport ρ) :
    (fun x => (A x).mulVec (fun j => ∫ s in Set.Ioo a b, ρ s * G (s,x) j)) =ᵐ[volume.restrict U]
      (fun x j => ∫ s in Set.Ioo a b, ρ s * (A x).mulVec (G (s,x)) j) := by
  let μ := volume.restrict (Set.Ioo a b)
  let ν := volume.restrict U
  have hp : volume.restrict (Set.Ioo a b ×ˢ U) = μ.prod ν := by
    simp only [μ,ν,Measure.volume_eq_prod,Measure.prod_restrict]
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioo a b ×ˢ U)) := by
    rw [hp]
    infer_instance
  obtain ⟨C,hC⟩ := hρc.exists_bound_of_continuous hρ
  have hF j : Integrable (fun z : ℝ × Vec d => ρ z.1 * G z j) (μ.prod ν) := by
    rw [← hp]
    simpa only [mul_comm] using
      ((parabolicSolution_gradient_coordinate_memLp hsol j).integrable (by norm_num)).mul_bdd
        ((hρ.measurable.comp measurable_fst).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun z => hC z.1)
  filter_upwards [ae_all_iff.mpr fun j => (hF j).prod_left_ae] with x hx
  funext i
  rw [matrix_coordinate_integral_components μ (A x) (fun s j => ρ s * G (s,x) j) hx i]
  apply integral_congr_ae
  filter_upwards with s
  simp only [Matrix.mulVec,dotProduct,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

end EinsteinRelation.Correctors
