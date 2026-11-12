import EinsteinRelation.Correctors.AKMParabolicIntegrability
import EinsteinRelation.Correctors.SpatialWeakLocalization

/-! # Integrable spatial pairings of parabolic solutions

Source: `paper/main.tex:808–816,822–840`. The actual energy class
makes the time-dependent scalar and flux pairings integrable. These are
the quantities whose weak time equation is integrated, with genuine
Bochner integrability at every step.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

private theorem integrable_spatial_weight {d : ℕ} {a b : ℝ} {U : Set (Vec d)}
    (f : ℝ × Vec d → ℝ)
    (hf : Integrable f (volume.restrict (Set.Ioo a b ×ˢ U)))
    {ψ : Vec d → ℝ} (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    Integrable (fun z : ℝ × Vec d => f z * ψ z.2)
      (volume.restrict (Set.Ioo a b ×ˢ U)) := by
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hψ
  exact hf.mul_bdd (hψ.comp continuous_snd).measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => hC z.2)

/-- Both separated spatial pairings in the parabolic weak time equation
are genuinely integrable in time on a finite-volume spatial domain.
Source: `paper/main.tex:808–816,822–840`. -/
theorem parabolicSolution_spatial_pairings_integrable {d : ℕ} {K a b : ℝ}
    (hK : 0 < K) (A : Coefficient d K) {U : Set (Vec d)}
    [IsFiniteMeasure (volume.restrict U)]
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsParabolicSolution A (Set.Ioo a b) U u G)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) :
    Integrable (fun t => ∫ x in U, u (t, x) * ψ x) (volume.restrict (Set.Ioo a b)) ∧
      Integrable (fun t => ∫ x in U,
        dot ((A x).mulVec (G (t, x))) (gradient ψ x))
        (volume.restrict (Set.Ioo a b)) := by
  let ν : Measure (ℝ × Vec d) := volume.restrict (Set.Ioo a b ×ˢ U)
  haveI : IsFiniteMeasure ν := by
    dsimp [ν]
    rw [Measure.volume_eq_prod ℝ (Vec d), ← Measure.prod_restrict]
    infer_instance
  have hu : Integrable (fun z : ℝ × Vec d => u z * ψ z.2) ν :=
    integrable_spatial_weight u (hsol.1.integrable one_le_two) hψ.continuous hc
  have hf : Integrable (fun z : ℝ × Vec d =>
      dot ((A z.2).mulVec (G z)) (gradient ψ z.2)) ν := by
    apply integrable_finset_sum Finset.univ
    intro j _
    exact integrable_spatial_weight _
      ((parabolicSolution_flux_coordinate_memLp hK A hsol j).integrable one_le_two)
      ((contDiff_infty_iff_fderiv.mp hψ).2.clm_apply contDiff_const).continuous
      (hc.fderiv_apply ℝ (unitVector j))
  have hν : ν = (volume.restrict (Set.Ioo a b)).prod (volume.restrict U) := by
    dsimp [ν]
    rw [Measure.volume_eq_prod ℝ (Vec d), Measure.prod_restrict]
  rw [hν] at hu hf
  exact ⟨hu.integral_prod_left, hf.integral_prod_left⟩

end EinsteinRelation.Correctors
