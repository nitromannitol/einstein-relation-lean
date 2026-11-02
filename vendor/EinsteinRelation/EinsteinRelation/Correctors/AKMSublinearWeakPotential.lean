import EinsteinRelation.Correctors.AKMScalarSublinearityTransport
import EinsteinRelation.Correctors.AKMFluxIdentification
import EinsteinRelation.Correctors.AKMGlobalWeakPotential
import EinsteinRelation.Correctors.AKMRapidScalarOrbitFactors
import EinsteinRelation.Correctors.MaximalGradientErrors
import EinsteinRelation.Correctors.ScalarOrbitBallSublinearity
import EinsteinRelation.Correctors.SpatialIntegerPropertiesPushforward
import EinsteinRelation.Correctors.SublinearWeakPotentialTransfer
import EinsteinRelation.Calculus.SpatialEqualityPushforward

/-!
# Sublinear global weak potentials under the actual coefficient law

Source: `paper/main.tex:693-702`. Only countable spatial integral events
are transported through the project map. The global weak potential is
constructed under the raw law first; Poincaré and the transported maximal
errors then prove its full-radius sublinearity on that same law.
-/

open MeasureTheory Filter Topology
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger Environment.AKMTestIntegralSupport ReductionImageV3
open StationarySpatialRealization

/-- The canonical raw gradient has an actual global, locally L² weak
potential whose normalized L² oscillation is sublinear at every real radius. -/
theorem exists_akm_sublinear_global_weakPotential
    (hP : BallPoincareEstimate) {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    ∃ G : Coefficient d (AKMUpperEllipticity L) → Vec d → EuclideanSpace ℝ (Fin d),
      Measurable (fun p : Coefficient d (AKMUpperEllipticity L) × Vec d => G p.1 p.2) ∧
      (∀ᵐ a ∂actualCoefficientLaw Q,
        (∀ R : ℝ, 0 < R → MemLp (G a) 2 (volume.restrict (ball 0 R))) ∧
        ∃ v : Vec d → ℝ, HasWeakGradient Set.univ v (fun x => (G a x).ofLp) ∧
          (∀ R : ℝ, 0 < R → MemLp v 2 (volume.restrict (ball 0 R))) ∧
          Tendsto (fun R : ℝ => R⁻¹ * Real.sqrt
            (⨍ x in ball 0 R, (v x - ⨍ y in ball 0 R, v y ∂volume)^2 ∂volume))
            atTop (𝓝 0)) ∧
      ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
        G (project (r₀ := r₀) Q.ellipticity_parameter ω) x =
          (canonicalCorrectorGradient Q i :
            Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
              (translate x (reduce ω.1)) := by
  obtain ⟨G, hG, hpot, hidG⟩ := exists_akm_canonical_global_weakPotential hP Q i
  obtain ⟨f, u, g, W, hm, hW, hrapid, hid⟩ := exists_akm_rapid_scalar_orbit_factors Q i
  let π := project (d := d) (r₀ := r₀) Q.ellipticity_parameter
  have hπ := measurable_project (d := d) (r₀ := r₀) Q.ellipticity_parameter
  let H := (canonicalCorrectorGradient Q i :
    Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
  let D := fun n => horizontalEuclideanGradient (reducedEnvironmentLaw Q)
    (reducedEnvironmentLaw_stationary Q) (f n)
  have hGsource := (measurePreserving_physicalReduction Q).quasiMeasurePreserving.ae
    (ae_spatialRealization_memLp_on_all_compacts (reducedEnvironmentLaw_stationary Q) H)
  have hGcompact := ae_local_square_integrable_of_pullback
    (physicalReferenceLaw Q) π hπ G hG (by
      filter_upwards [hGsource, hidG] with ω hω hGω
      intro K hK
      exact (memLp_congr_ae (ae_restrict_of_ae hGω)).mpr (hω K hK))
  have hs := samplewise_scalar_gradient_approximation_of_rapid
    (reducedEnvironmentLaw Q) (reducedEnvironmentLaw_stationary Q) H f hrapid
  have hlD := ae_all_iff.mpr fun n => ae_spatialRealization_memLp_on_all_compacts
    (reducedEnvironmentLaw_stationary Q) (D n)
  have hsource := (measurePreserving_physicalReduction Q).quasiMeasurePreserving.ae (hs.and hlD)
  have hlocal : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ n (K : Set (Vec d)), IsCompact K →
      MemLp (u n (π ω)) 2 (volume.restrict K) ∧
      MemLp (g n (π ω)) 2 (volume.restrict K) := by
    filter_upwards [hsource, hid] with ω hω hidω
    intro n K hK
    exact ⟨(memLp_congr_ae (ae_restrict_of_ae (hidω.1 n))).mpr (hω.1.2.1 n K hK),
      (memLp_congr_ae (ae_restrict_of_ae (hidω.2.1 n))).mpr (hω.2 n K hK)⟩
  have hweak : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ n,
      HasWeakGradient Set.univ (u n (π ω)) (fun x => (g n (π ω) x).ofLp) := by
    filter_upwards [hsource, hid] with ω hω hidω
    intro n j
    apply (hω.1.1 n j).congr_ae
    · simpa only [Measure.restrict_univ] using (hidω.1 n).symm
    · simpa only [Measure.restrict_univ, π] using!
        (hidω.2.1 n).symm.mono fun x hx => congrArg (fun z => z.ofLp j) hx
  have hu (n : ℕ) := ae_local_square_integrable_of_pullback
    (physicalReferenceLaw Q) π hπ (u n) (hm n).1
    (hlocal.mono fun ω hω K hK => (hω n K hK).1)
  have hg (n : ℕ) := ae_local_square_integrable_of_pullback
    (physicalReferenceLaw Q) π hπ (g n) (hm n).2
    (hlocal.mono fun ω hω K hK => (hω n K hK).2)
  let J := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).toContinuousLinearMap
  have hw (n : ℕ) := ae_spatial_weakGradient_of_pullback
    (physicalReferenceLaw Q) π hπ (u n) (fun a x => (g n a x).ofLp)
    (hm n).1 (J.continuous.measurable.comp (hm n).2)
    (hlocal.mono fun ω hω K hK => ⟨(hω n K hK).1, J.comp_memLp' (hω n K hK).2⟩)
    (hweak.mono fun ω hω => hω n)
  have hscalar (n : ℕ) := ae_akm_scalar_integerCube_sublinearity Q
    (f n : Lp ℝ 2 (reducedEnvironmentLaw Q)) (u n) (hm n).1
    (hid.mono fun ω hω => hω.1 n)
  have hmaxSource := (measurePreserving_physicalReduction Q).quasiMeasurePreserving.ae
    (ae_uniform_integerCube_gradient_errors_of_rapid
      (reducedEnvironmentLaw Q) (reducedEnvironmentLaw_stationary Q) D H hrapid)
  have hmax := ae_integerCube_uniform_errors_of_pullback (physicalReferenceLaw Q) π hπ
    g G (fun n => (hm n).2) hG (by
      filter_upwards [hmaxSource, hid, hidG] with ω hω hidω hGω
      apply hω.mono
      intro n hn k
      have he : (⨍ x in Metric.closedBall (0 : Vec d) ((k : ℝ) + 1),
          ‖g n (π ω) x - G (π ω) x‖^2 ∂volume) =
          ⨍ x in Metric.closedBall (0 : Vec d) ((k : ℝ) + 1),
            ‖D n (translate x (reduce ω.1)) - H (translate x (reduce ω.1))‖^2 ∂volume := by
        apply average_congr
        filter_upwards [ae_restrict_of_ae (hidω.2.1 n), ae_restrict_of_ae hGω] with x hx hy
        rw [hx, hy]
      exact he.trans_le (hn k))
  obtain ⟨C, hC, hcompare⟩ := exists_ball_average_le_cube_average d
  refine ⟨G, hG, ?_, hidG⟩
  filter_upwards [hpot, ae_all_iff.mpr hu, ae_all_iff.mpr hg,
    ae_all_iff.mpr hw, ae_all_iff.mpr hscalar, hmax, hGcompact]
    with a hpa hua hga hwa hsa hma hGc
  obtain ⟨v, hwv, hv, _⟩ := hpa.2
  refine ⟨hpa.1, v, hwv, hv, ?_⟩
  refine sublinear_weakPotential_of_rapid_approximation hP (Fact.out : 2 ≤ d)
    v (G a) (fun n => u n a) (fun n => g n a) hv hpa.1 ?_ ?_ hwv hwa ?_ C ?_
  · intro n R hR
    exact (hua n _ (isCompact_closedBall (0 : Vec d) R)).mono_measure
      (Measure.restrict_mono_set volume (euclideanBall_subset_coordinateClosedBall R hR.le))
  · intro n R hR
    exact (hga n _ (isCompact_closedBall (0 : Vec d) R)).mono_measure
      (Measure.restrict_mono_set volume (euclideanBall_subset_coordinateClosedBall R hR.le))
  · intro n
    apply ball_scaled_means_zero_of_integerCube_scaled_means_zero _ (fun _ => sq_nonneg _) ?_ (hsa n)
    intro R hR
    simpa only [sq_abs, IntegrableOn] using!
      (hua n _ (isCompact_closedBall (0 : Vec d) R)).integrable_sq
  · apply hma.mono
    intro n hn R hR
    let k : ℕ := ⌊R⌋₊
    have hRpos : 0 < R := zero_lt_one.trans_le hR
    have hlow : R ≤ (k : ℝ) + 1 := (Nat.lt_floor_add_one R).le
    have hhigh : (k : ℝ) + 1 ≤ 2 * R := by
      have hk : (k : ℝ) ≤ R := Nat.floor_le hRpos.le
      linarith
    let K := Metric.closedBall (0 : Vec d) ((k : ℝ) + 1)
    have he := (hga n K (isCompact_closedBall _ _)).sub (hGc K (isCompact_closedBall _ _))
    exact (hcompare R ((k : ℝ) + 1) hRpos hlow hhigh _ (fun _ => sq_nonneg _)
      ((memLp_two_iff_integrable_sq_norm he.aestronglyMeasurable).mp he)).trans
      (mul_le_mul_of_nonneg_left (hn k) hC.le)

end EinsteinRelation.Correctors
