import EinsteinRelation.Correctors.CanonicalScalarLocalRegularity

/-! Source: `paper/main.tex:694-704,735-737`. The actual canonical
variational gradient has affine C¹,α representatives on every ball.
The same underlying weak potential is used at every radius. -/

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger StationarySpatialRealization

/-- Local GT regularity for the canonical affine potential, retaining
both its value class and its actual gradient class on one common event. -/
theorem ae_canonicalAffine_c1Alpha_representatives
    (hP : BallPoincareEstimate) (h836 : InteriorRegularRepresentative)
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    ∀ᵐ ω ∂reducedEnvironmentLaw Q, ∃ u : Vec d → ℝ,
      HasWeakGradient Set.univ u (fun x =>
        ((canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2
          (reducedEnvironmentLaw Q)) (translate x ω)).ofLp) ∧
      (∀ R : ℝ, 0 < R → MemLp u 2 (volume.restrict (ball 0 R))) ∧
      ∀ R : ℝ, 0 < R → ∃ (v : Vec d → ℝ) (h : Vec d → Vec d),
        C1Alpha (ball 0 R) (1 / 2) v h ∧
        v =ᵐ[volume.restrict (ball 0 R)] (fun x => x i + u x) ∧
        h =ᵐ[volume.restrict (ball 0 R)] (fun x => unitVector i +
          ((canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2
            (reducedEnvironmentLaw Q)) (translate x ω)).ofLp) := by
  let G : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q) :=
    canonicalCorrectorGradient Q i
  have hL : 0 ≤ L := zero_le_one.trans Q.ellipticity_parameter
  filter_upwards [ae_exists_canonical_global_weakPotential hP Q i,
    ae_spatialRealization_memLp_on_all_compacts (reducedEnvironmentLaw_stationary Q) G,
    ae_canonicalCorrectorFlux_hasWeakDivergence Q i,
    ae_spatial_canonicalCorrectorFlux Q i measurable_id,
    ActualImageLpStateTransport.ae_reducedEnvironmentLaw_mem_image Q]
    with ω hu hG hdiv hflux himg
  obtain ⟨u, hw, hu, _⟩ := hu
  have hdiv' : HasWeakDivergence Set.univ
      (fun x => (ω.1 x).mulVec (unitVector i + (G (translate x ω)).ofLp))
      (fun _ => 0) := by
    exact hdiv.congr_ae (by simpa only [Measure.restrict_univ] using hflux)
      (ae_eq_refl _)
  obtain ⟨η, hη, hηeq⟩ := himg
  have hb := sourceReducedBound_support Q.ellipticity_parameter hη
  have hB : 0 < sourceReducedBound L := zero_lt_one.trans_le hb.1
  have hell : IsElliptic (sourceReducedBound L) ω.1 := by
    simpa only [← hηeq] using hb.2.1
  have hlip : IsOperatorLipschitz (Real.exp (2 * L) * (L + 2 * L ^ 2)) ω.1 := by
    simpa only [← hηeq] using hb.2.2.2.1
  refine ⟨u, hw, hu, ?_⟩
  intro R hR
  have hg : MemLp (fun x => (G (translate x ω)).ofLp) 2
      (volume.restrict (ball (0 : Vec d) (2 * R))) := by
    apply memLp_pi_iff.mpr
    intro j
    exact ((hG (Metric.closedBall 0 (2 * R)) (isCompact_closedBall _ _)).mono_measure
      (Measure.restrict_mono_set volume
        (euclideanBall_subset_coordinateClosedBall (2 * R) (by positivity)))).eval_piLp j
  exact exists_c1Alpha_affine_corrector_ball_of_gt h836 (Fact.out : 2 ≤ d) ω.1
    (sourceReducedBound L) (Real.exp (2 * L) * (L + 2 * L ^ 2)) R hB (by positivity) hR
    hell hlip i u _ (hu _ (by positivity)) hg
    (fun j => HasWeakPartialDerivative.restrict_subset (Set.subset_univ _) MeasurableSet.univ (hw j))
    (HasWeakDivergence.restrict_subset (Set.subset_univ _) MeasurableSet.univ hdiv')

end EinsteinRelation.Correctors
