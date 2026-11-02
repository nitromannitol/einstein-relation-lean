import EinsteinRelation.Correctors.SpatialWeakLocalization
import EinsteinRelation.Correctors.AKMPotentialGradientTransfer
import EinsteinRelation.Correctors.AffineWeakSolutionOnBalls
import EinsteinRelation.Correctors.CanonicalHarmonicFromPoincare
import EinsteinRelation.Correctors.SpatialBallTranslation
import EinsteinRelation.Calculus.WeakGradientSubtraction
import EinsteinRelation.Correctors.WeakGradientCentering
import EinsteinRelation.Correctors.SpatialBallLocalL2Support
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger
open Environment.AKMTestIntegralSupport ReductionImageV3
/-- Source: `paper/main.tex:727-731`. The actual rescaled AKM potential
has the canonical weak gradient and solves the affine harmonic equation
on every ball, in every scalar gauge. -/
theorem ae_physicalAKMPotential_affine_weakSolution
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (halfDirection i))
    (hid : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
      (2 : ℝ) • (halfDirection i + φ.grad
        (project (r₀ := r₀) Q.ellipticity_parameter ω) y) =
      (correctorUnitVector i + (canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
          (translate (r₀ • y) (reduce ω.1))).ofLp) :
    ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ (z : Vec d) (r : ℝ), 0 < r → ∀ c : ℝ,
      MemLp (fun x => (2 * r₀) * φ.potential
        (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x) - c)
        2 (volume.restrict (ball z r)) ∧
      WeakSolution (ball z r) (reduce ω.1).1
        (fun x => x i - z i + (2 * r₀) * φ.potential
          (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x) - c)
        (fun x => unitVector i + ((canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (translate x (reduce ω.1))).ofLp) := by
  have hr : 0 < r₀ := zero_lt_one.trans_le Q.range_parameter
  let G : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q) :=
    canonicalCorrectorGradient Q i
  have hw := ae_akmPotential_has_canonical_weakGradient Q i φ hid
  have hu := (measurePreserving_akmProject Q).quasiMeasurePreserving.ae
    φ.locally_square_integrable
  have hg := (measurePreserving_physicalReduction Q).quasiMeasurePreserving.ae
    (StationarySpatialRealization.ae_spatialRealization_memLp_on_all_compacts (reducedEnvironmentLaw_stationary Q) G)
  have hd := (measurePreserving_physicalReduction Q).quasiMeasurePreserving.ae
    (ae_canonicalCorrectorFlux_hasWeakDivergence Q i)
  have hf := (measurePreserving_physicalReduction Q).quasiMeasurePreserving.ae
    (ae_spatial_canonicalCorrectorFlux Q i measurable_id)
  filter_upwards [hw, hu, hg, hd, hf] with ω hweak hlocal hG hdiv hflux
  let u : Vec d → ℝ := fun x => (2 * r₀) * φ.potential
    (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x)
  let g : Vec d → Vec d := fun x => (G (translate x (reduce ω.1))).ofLp
  have hu0 : ∀ R : ℝ, 0 < R → MemLp u 2 (volume.restrict (ball 0 R)) := by
    simpa only [smul_eq_mul] using memLp_two_on_euclidean_balls_dilation _
      (fun R hR => (hlocal R hR).1) r₀⁻¹ (2 * r₀) (inv_pos.mpr hr)
  have hg0 : ∀ R : ℝ, 0 < R → MemLp g 2 (volume.restrict (ball 0 R)) := by
    intro R hR
    apply memLp_pi_iff.mpr
    intro j
    exact ((hG (Metric.closedBall 0 R) (isCompact_closedBall _ _)).mono_measure
      (Measure.restrict_mono_set volume
        (euclideanBall_subset_coordinateClosedBall R hR.le))).eval_piLp j
  intro z r hrpos c
  letI : IsFiniteMeasure (volume.restrict (ball z r)) :=
    isFiniteMeasure_restrict_euclideanBall z r hrpos
  have huz := memLp_on_euclideanBall_of_origin_balls u hu0 z r hrpos
  have hgz := memLp_on_euclideanBall_of_origin_balls g hg0 z r hrpos
  have huc : MemLp (fun x => u x - c) 2 (volume.restrict (ball z r)) :=
    huz.sub (memLp_const c)
  refine ⟨huc, affine_weakSolution_on_ball_of_weakPotential z r hrpos i
    (reduce ω.1).1 u g c huc hgz ?_ ?_⟩
  · exact hasWeakGradient_mono (Set.subset_univ _)
      (hasWeakGradient_sub_const Set.univ hweak c)
  · apply (HasWeakDivergence.restrict_subset (Set.subset_univ _)
      MeasurableSet.univ hdiv).congr_ae (ae_restrict_of_ae hflux) (ae_eq_refl _)
end EinsteinRelation.Correctors
