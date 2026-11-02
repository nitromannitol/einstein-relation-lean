import EinsteinRelation.Correctors.StationarySpatialWeakPotentials
import EinsteinRelation.Correctors.AffineWeakSolution
import EinsteinRelation.Correctors.SpatialDivergenceFixedTest
import EinsteinRelation.Correctors.StationarySpatialWeakDivergence
import EinsteinRelation.Correctors.GTRegularPotentialConstruction
import EinsteinRelation.Correctors.AKMFluxIdentification

/-!
# Constructing the canonical harmonic realization

Source: `paper/main.tex:693-698,727-729`. The actual closed variational
corrector gradient has local scalar weak potentials by Poincaré. Its
variational flux is divergence-free in space. Interior GT regularity
therefore supplies the canonical harmonic realization.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger StationarySpatialRealization

/-- The actual variational canonical flux is samplewise divergence-free. -/
theorem ae_canonicalCorrectorFlux_hasWeakDivergence {d : ℕ} [Fact (2 ≤ d)]
    {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    ∀ᵐ ω ∂reducedEnvironmentLaw Q, HasWeakDivergence Set.univ
      (fun x => (canonicalCorrectorFlux Q i (translate x ω)).ofLp) (fun _ => 0) := by
  apply SpatialDivergence.ae_hasWeakDivergence_of_ae_fixedTest
    (reducedEnvironmentLaw Q) (reducedEnvironmentLaw_stationary Q)
    (canonicalCorrectorFlux Q i)
  intro ψ
  exact ae_spatial_divergence_fixedTest (reducedEnvironmentLaw Q)
    (reducedEnvironmentLaw_stationary Q) (canonicalCorrectorFlux Q i)
    (canonicalCorrectorGradient_variational_horizontalH1 Q i)
    ψ ψ.contDiff ψ.hasCompactSupport

/-- The doubled-ball scalar weak-solution premise is obtained internally
from the actual canonical gradient, with no realization assumption. -/
theorem ae_canonical_doubledBall_weakSolution
    (hP : BallPoincareEstimate) {d : ℕ} [Fact (2 ≤ d)]
    {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    ∀ᵐ ω ∂reducedEnvironmentLaw Q, ∃ (u : Vec d → ℝ) (g : Vec d → Vec d),
      WeakSolution (ball 0 2) ω.1 u g ∧
      (∀ᵐ x ∂volume.restrict (ball (0 : Vec d) 2),
        g x = (correctorUnitVector i + (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (translate x ω)).ofLp) := by
  let G := (canonicalCorrectorGradient Q i :
    Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
  filter_upwards [ae_exists_spatial_weakPotential_of_closed_gradient hP
      (reducedEnvironmentLaw Q) (reducedEnvironmentLaw_stationary Q)
      G (canonicalCorrectorGradient Q i).property,
    ae_spatialRealization_memLp_on_all_compacts (reducedEnvironmentLaw_stationary Q) G,
    ae_canonicalCorrectorFlux_hasWeakDivergence Q i,
    ae_spatial_canonicalCorrectorFlux Q i measurable_id] with ω hpot hG hdiv hflux
  obtain ⟨u, hu, hweak⟩ := hpot 2 (by norm_num)
  have hg : MemLp (fun x => (G (translate x ω)).ofLp) 2
      (volume.restrict (ball (0 : Vec d) 2)) := by
    apply memLp_pi_iff.mpr
    intro j
    exact ((hG (Metric.closedBall 0 2) (isCompact_closedBall _ _)).mono_measure
      (Measure.restrict_mono_set volume
        (euclideanBall_subset_coordinateClosedBall 2 (by norm_num)))).eval_piLp j
  have hd : HasWeakDivergence (ball (0 : Vec d) 2)
      (fun x => (ω.1 x).mulVec (unitVector i + (G (translate x ω)).ofLp))
      (fun _ => 0) := by
    apply (HasWeakDivergence.restrict_subset (Set.subset_univ _) MeasurableSet.univ hdiv).congr_ae
      (ae_restrict_of_ae hflux) (ae_eq_refl _)
  refine ⟨(fun x => x i + u x), (fun x => unitVector i + (G (translate x ω)).ofLp),
    affine_weakSolution_of_weakPotential 2 (by norm_num) i ω.1 u _ hu hg hweak hd, ?_⟩
  exact ae_of_all _ fun _ => rfl

/-- Existing deterministic GT inputs now suffice for the canonical harmonic
realization; scalar potentials and divergence are internal constructions. -/
theorem canonicalHarmonicRealization_of_gt
    (hP : BallPoincareEstimate) (h836 : InteriorRegularRepresentative) :
    CanonicalHarmonicRealization := by
  apply canonicalHarmonicRealization_of_gt_and_weak_potentials h836
  intro d hd L r₀ Q i
  letI : Fact (2 ≤ d) := ⟨hd⟩
  exact ae_canonical_doubledBall_weakSolution hP Q i

end EinsteinRelation.Correctors
