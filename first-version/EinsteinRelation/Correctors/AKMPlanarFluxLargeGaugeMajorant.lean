import EinsteinRelation.Correctors.AKMPlanarFourEightMoments
import EinsteinRelation.Correctors.AKMPlanarOscillationMeasurability
import EinsteinRelation.Correctors.AKMPlanarFluxOscillationMeasurability
import EinsteinRelation.Correctors.AKMPlanarAllCenterFluxMoments
import EinsteinRelation.Correctors.RootIntegralGaugeComparison
import EinsteinRelation.Correctors.RootIntegralAverage
import EinsteinRelation.Correctors.SpatialBallLocalL2Support
import EinsteinRelation.Correctors.LocalMomentMeasurability
import EinsteinRelation.Correctors.TwoMajorantMoments
import EinsteinRelation.Correctors.CorrectorAmplitudeLowerBound
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport ReductionImageV3
/-- Source: `paper/main.tex:718-723`. A measurable majorant for the radius-four tensor
L² norm in the large-radius gauge retains the logarithmic moment bound.
The tensor source carries a jointly measurable potential. Constants precede the law and all centers. -/
theorem akm_planar_flux_large_heat_gauge_L2_majorant
    (h615 : FluxPlanarL2Estimate) (h616 : FluxHeatDifferenceEstimate)
    (L p : ℝ) (hK : 1 < AKMUpperEllipticity L) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ {r₀ : ℝ} (Q : EnvironmentLaw 2 L r₀) (i : Fin 2)
      (φ : Corrector (actualCoefficientLaw Q) (halfDirection i)),
      (∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ v ∂(volume : Measure (Vec 2)),
        (2 : ℝ) • (halfDirection i + φ.grad
          (project (r₀ := r₀) Q.ellipticity_parameter ω) v) =
          (correctorUnitVector i + (canonicalCorrectorGradient Q i :
            Lp (EuclideanSpace ℝ (Fin 2)) 2 (reducedEnvironmentLaw Q))
              (translate (r₀ • v) (reduce ω.1))).ofLp) →
      ∀ (S : FluxCorrector (scaledAKMCorrector φ 2)) (r R : ℝ), 1 ≤ r → 1 ≤ R → ∀ (z y : Vec 2),
      euclideanNorm (z - y) ≤ 2 * R + 4 →
      ∃ M : Coefficient 2 (AKMUpperEllipticity L) → ℝ,
        AEMeasurable M (actualCoefficientLaw Q) ∧
        (∀ a, 0 ≤ M a) ∧
        (∀ᵐ a ∂actualCoefficientLaw Q,
          Real.sqrt (∫ x in ball (r⁻¹ • z) 4,
            frobeniusNorm (S.potential a x - fluxHeatAverage (S.potential a) (r⁻¹ • y) (8 * R)) ^ 2
              ∂volume) ≤ M a) ∧
        (∫⁻ a, ENNReal.ofReal (M a ^ p) ∂actualCoefficientLaw Q) ≤
          ENNReal.ofReal (C * (Real.sqrt (Real.log (2 + R))) ^ p) := by
  obtain ⟨C₀, hC₀, hosc⟩ := akm_planar_flux_allCenter_L2_moments h615 L p hK (by linarith)
  obtain ⟨C₁, hC₁, hheat⟩ := akm_planar_flux_four_eight_heat_moments
    h616 (AKMUpperEllipticity L) p hK (by linarith)
  let V := volume.real (ball (0 : Vec 2) 4)
  let K := 2 * Real.sqrt V
  let B := C₀ * (Real.sqrt (Real.log 4)) ^ (p / 2)
  have hV : 0 < V := ball_volume_pos_finite 2 4 (by norm_num)
  have hK0 : 0 < K := by dsimp [K]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨K ^ p * 2 ^ p * (B + C₁), by positivity, ?_⟩
  intro r₀ Q i φ hid S r R hr hR z y hzy
  let A (a : Coefficient 2 (AKMUpperEllipticity L)) :=
    Real.sqrt (⨍ x in ball (r⁻¹ • z) 4,
      frobeniusNorm (S.potential a x - fluxHeatAverage (S.potential a) (r⁻¹ • z) 4) ^ 2 ∂volume)
  let D (a : Coefficient 2 (AKMUpperEllipticity L)) :=
    frobeniusNorm (fluxHeatAverage (S.potential a) (r⁻¹ • z) 4 -
      fluxHeatAverage (S.potential a) (r⁻¹ • y) (8 * R))
  let T := (Real.sqrt (Real.log (2 + R))) ^ p
  have hT : 1 ≤ T := by
    have hs : 1 ≤ Real.sqrt (Real.log (2 + R)) := by
      simpa [correctorAmplitude] using one_le_correctorAmplitude 2 hR
    simpa only [Real.one_rpow] using Real.rpow_le_rpow zero_le_one hs (by linarith : 0 ≤ p)
  have ham : AEMeasurable A (actualCoefficientLaw Q) :=
    (measurable_tensor_local_average_root S.potential
      (fun a => fluxHeatAverage (S.potential a) (r⁻¹ • z) 4) S.measurable_potential
      (measurable_fluxHeatAverage S.potential S.measurable_potential (r⁻¹ • z) 4)
      (r⁻¹ • z) 4).aemeasurable
  have hdm : AEMeasurable D (actualCoefficientLaw Q) := by
    obtain ⟨_, _, hh⟩ := h616 (AKMUpperEllipticity L) 1 hK zero_lt_one one_lt_two
    exact (hh (actualCoefficientLaw Q) (lawHypotheses_actualCoefficientLaw Q)
      ((2 : ℝ) • halfDirection i) (euclideanNorm_two_smul_halfDirection i)
      (scaledAKMCorrector φ 2) S 4 (8 * R) (by norm_num)
      ((four_eight_scale_geometry r R (euclideanNorm (z - y)) hr hR
        (by unfold euclideanNorm; positivity) hzy).1) (r⁻¹ • z) (r⁻¹ • y)).1.aemeasurable
  have ha : ∀ a, 0 ≤ A a := fun _ => Real.sqrt_nonneg _
  have hd : ∀ a, 0 ≤ D a := fun _ => Real.sqrt_nonneg _
  have hA : (∫⁻ a, ENNReal.ofReal (A a ^ p) ∂actualCoefficientLaw Q) ≤
      ENNReal.ofReal (B * T) :=
    (hosc Q i φ hid S (r⁻¹ • z) 4 (by norm_num)).trans
      (ENNReal.ofReal_le_ofReal (le_mul_of_one_le_right hB.le hT))
  have hD : (∫⁻ a, ENNReal.ofReal (D a ^ p) ∂actualCoefficientLaw Q) ≤
      ENNReal.ofReal (C₁ * T) :=
    hheat (actualCoefficientLaw Q) (lawHypotheses_actualCoefficientLaw Q)
      ((2 : ℝ) • halfDirection i) (euclideanNorm_two_smul_halfDirection i)
      (scaledAKMCorrector φ 2) S r R hr hR z y hzy
  let M := fun a => K * (A a + D a)
  have hM0 : ∀ a, 0 ≤ M a := fun a => mul_nonneg hK0.le (add_nonneg (ha a) (hd a))
  have hMm : AEMeasurable M (actualCoefficientLaw Q) :=
    aemeasurable_const.mul (ham.add hdm)
  refine ⟨M, hMm, hM0, ?_, ?_⟩
  · filter_upwards [S.locally_square_integrable] with a hlocal
    letI := isFiniteMeasure_restrict_euclideanBall (r⁻¹ • z) 4 (by norm_num)
    have hu (j k : Fin 2) := memLp_on_euclideanBall_of_origin_balls
      (fun x => S.potential a x j k) (fun t ht => (hlocal t ht j k).1)
      (r⁻¹ • z) 4 (by norm_num)
    have hmass : (volume.restrict (ball (r⁻¹ • z) 4)).real Set.univ = V := by
      simp only [measureReal_def, Measure.restrict_apply_univ, volume_euclideanBall_center, V]
    have havg := sqrt_integral_eq_sqrt_mass_mul_sqrt_average
      (volume.restrict (ball (r⁻¹ • z) 4))
      (fun x => frobeniusNorm (S.potential a x - fluxHeatAverage (S.potential a) (r⁻¹ • z) 4) ^ 2)
      (by rw [hmass]; exact hV)
    have h := root_integral_tensor_gauge_comparison
      (volume.restrict (ball (r⁻¹ • z) 4)) (S.potential a) hu
      (fluxHeatAverage (S.potential a) (r⁻¹ • z) 4)
      (fluxHeatAverage (S.potential a) (r⁻¹ • y) (8 * R))
    rw [hmass, havg, hmass] at h
    exact h.trans_eq (by dsimp [M, K, A, D]; ring)
  · have h := lintegral_rpow_le_of_two_majorants (actualCoefficientLaw Q)
      M A D K p (B * T) (C₁ * T) hK0.le (by linarith) ha hd ham hdm
      (ae_of_all _ fun a => ⟨hM0 a, le_rfl⟩) hA hD
    rw [max_eq_left (mul_nonneg hB.le (by linarith)),
      max_eq_left (mul_nonneg hC₁.le (by linarith))] at h
    convert h using 1
    congr 1
    ring
end EinsteinRelation.Correctors
