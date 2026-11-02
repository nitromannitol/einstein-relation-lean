import EinsteinRelation.Correctors.CanonicalHarmonicFromPoincare
import EinsteinRelation.Correctors.AKMCarrierIdentificationCellFluxAssembly
import EinsteinRelation.Correctors.SpatialWeakDilation
import EinsteinRelation.Correctors.SpatialLocalL2Dilation
import EinsteinRelation.Correctors.SpatialBallLocalL2
import EinsteinRelation.Correctors.SpatialDivergencePushforward
import EinsteinRelation.Correctors.AKMSpatialFluxIdentification

/-!
# Harmonicity on the actual AKM coefficient law

Source: `paper/main.tex:693-702,727-729`. Transport the measurable
reconstructed flux through fixed divergence tests, then replace the
reconstructed coefficient by the raw coefficient on their proved common
full-law event. The project map is used only for measurable events.
-/
open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport ReductionImageV3
open StationarySpatialRealization

/-- Canonical flux divergence and the literal spatial gradient identity
imply the AKM harmonicity characterization for the raw coefficient field. -/
theorem ae_akm_harmonic_of_canonical_gradient
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (g : Coefficient d (AKMUpperEllipticity L) → Vec d → Vec d)
    (hg : Measurable (fun p : Coefficient d (AKMUpperEllipticity L) × Vec d => g p.1 p.2))
    (hid : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
      (2 : ℝ) • (halfDirection i + g (project (r₀ := r₀) Q.ellipticity_parameter ω) y) =
        (correctorUnitVector i + (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (translate (r₀ • y) (reduce ω.1))).ofLp) :
    ∀ᵐ a ∂actualCoefficientLaw Q, HasWeakDivergence Set.univ
      (fun x => (a x).mulVec (halfDirection i + g a x)) (fun _ => 0) := by
  obtain ⟨R, hR, hReq⟩ := exists_measurable_continuous_reconstruction
    (d := d) (K := AKMUpperEllipticity L)
  let π := project (d := d) (r₀ := r₀) Q.ellipticity_parameter
  have hπ := measurable_project (d := d) (r₀ := r₀) Q.ellipticity_parameter
  let J := fun (a : Coefficient d (AKMUpperEllipticity L)) (x : Vec d) =>
    (R a x).mulVec (halfDirection i + g a x)
  have hA : Measurable (fun p : Coefficient d (AKMUpperEllipticity L) × Vec d => R p.1 p.2) :=
    continuous_eval.measurable.comp ((hR.comp measurable_fst).prodMk measurable_snd)
  have hJ : Measurable (fun p : Coefficient d (AKMUpperEllipticity L) × Vec d => J p.1 p.2) :=
    (show Continuous (fun p : Mat d × Vec d => p.1.mulVec p.2) from
      continuous_fst.matrix_mulVec continuous_snd).measurable.comp
        (hA.prodMk (measurable_const.add hg))
  have hcoeff := ae_actualCoefficientLaw_field_eq_reconstruction Q R hR hReq
  have hcoeffSource := (measurePreserving_akmProject Q).quasiMeasurePreserving.ae hcoeff
  have heq : ∀ᵐ ω ∂physicalReferenceLaw Q, (fun x => J (π ω) x) =ᵐ[volume]
      (fun x => (ellipticityScale L / 2) •
        (canonicalCorrectorFlux Q i (translate (r₀ • x) (reduce ω.1))).ofLp) := by
    filter_upwards [ae_akmFlux_eq_scaled_canonicalFlux Q i g hid, hcoeffSource] with ω hω hc
    filter_upwards [hω, hc] with x hx hcx
    exact (congrArg (fun a : Mat d => a.mulVec (halfDirection i + g (π ω) x)) hcx).symm.trans hx
  have hsource := (measurePreserving_physicalReduction Q).quasiMeasurePreserving.ae
    ((ae_spatialRealization_memLp_on_all_compacts (reducedEnvironmentLaw_stationary Q)
      (canonicalCorrectorFlux Q i)).and (ae_canonicalCorrectorFlux_hasWeakDivergence Q i))
  have hr : 0 < r₀ := zero_lt_one.trans_le Q.range_parameter
  let C := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).toContinuousLinearMap
  have hregular : ∀ᵐ ω ∂physicalReferenceLaw Q,
      (∀ K : Set (Vec d), IsCompact K → MemLp (J (π ω)) 2 (volume.restrict K)) ∧
      HasWeakDivergence Set.univ (J (π ω)) (fun _ => 0) := by
    filter_upwards [hsource, heq] with ω hω he
    have hlocal (ρ : ℝ) (hρ : 0 < ρ) :
        MemLp (fun x => (canonicalCorrectorFlux Q i (translate x (reduce ω.1))).ofLp) 2
          (volume.restrict (ball 0 ρ)) :=
      C.comp_memLp' ((hω.1 _ (isCompact_closedBall (0 : Vec d) ρ)).mono_measure
        (Measure.restrict_mono_set volume (euclideanBall_subset_coordinateClosedBall ρ hρ.le)))
    have hscaled := memLp_two_on_euclidean_balls_dilation _ hlocal r₀
      (ellipticityScale L / 2) hr
    refine ⟨fun K hK => (memLp_congr_ae (ae_restrict_of_ae he)).mpr
      (memLp_on_compacts_of_euclidean_balls _ hscaled K hK), ?_⟩
    apply (hasWeakDivergence_zero_dilation _ hlocal hω.2 r₀ (ellipticityScale L / 2) hr).congr_ae
    · simpa only [Measure.restrict_univ] using he.symm
    · exact ae_eq_refl _
  have hraw := ae_weakDivergence_zero_of_pullback (physicalReferenceLaw Q) π hπ J hJ
    (hregular.mono fun _ h => h.1) (hregular.mono fun _ h => h.2)
  filter_upwards [hraw, hcoeff] with a ha hc
  apply ha.congr_ae
  · simp only [Measure.restrict_univ]
    filter_upwards [hc] with x hx
    exact congrArg (fun A : Mat d => A.mulVec (halfDirection i + g a x)) hx.symm
  · exact ae_eq_refl _

end EinsteinRelation.Correctors
