import EinsteinRelation.Correctors.AKMTranslatedFluxCorrector
import EinsteinRelation.Correctors.FluxHeatAverageTranslation
import EinsteinRelation.Correctors.AKMPlanarFixedScaleMoments
import EinsteinRelation.Correctors.AKMUnitFluxConstruction

/-!
# Planar flux L² moments at arbitrary centers

Source: `paper/main.tex:724-731`. Real stationarity of the actual coefficient
law transports AKM (6.15) to every center. The raw source gradient is tied
to the canonical gradient; potential-value stationarity is not assumed.
-/
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport ReductionImageV3

/-- The planar Frobenius oscillation estimate at every real center, with
the source's squared-norm exponent and its original constant order. -/
theorem akm_planar_flux_allCenter_L2_moments
    (h615 : FluxPlanarL2Estimate) (L p : ℝ)
    (hK : 1 < AKMUpperEllipticity L) (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ {r₀ : ℝ} (Q : EnvironmentLaw 2 L r₀) (i : Fin 2)
      (φ : Corrector (actualCoefficientLaw Q) (halfDirection i)),
      (∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec 2)),
        (2 : ℝ) • (halfDirection i + φ.grad
          (project (r₀ := r₀) Q.ellipticity_parameter ω) y) =
          (correctorUnitVector i + (canonicalCorrectorGradient Q i :
            Lp (EuclideanSpace ℝ (Fin 2)) 2 (reducedEnvironmentLaw Q))
              (translate (r₀ • y) (reduce ω.1))).ofLp) →
      ∀ (S : FluxCorrector (scaledAKMCorrector φ 2)) (z : Vec 2) (r : ℝ), 2 ≤ r →
      (∫⁻ a, ENNReal.ofReal ((Real.sqrt (⨍ x in ball z r,
        frobeniusNorm (S.potential a x -
          fluxHeatAverage (S.potential a) z r) ^ 2 ∂volume)) ^ p)
        ∂actualCoefficientLaw Q) ≤
        ENNReal.ofReal (C * (Real.sqrt (Real.log r)) ^ (p / 2)) := by
  obtain ⟨C, hC, hest⟩ := akm_planar_flux_L2_moments h615 (AKMUpperEllipticity L) p hK hp
  refine ⟨C, hC, ?_⟩
  intro r₀ Q i φ hid S z r hr
  have hc : ∀ᵐ a ∂actualCoefficientLaw Q, ∀ᵐ x ∂(volume : Measure (Vec 2)),
      (scaledAKMCorrector φ 2).grad (translateCoefficient (-z) a) (x + z) =
        (scaledAKMCorrector φ 2).grad a x := by
    filter_upwards [ae_inverse_translated_canonicalAKMGradient Q i φ hid z] with a ha
    filter_upwards [ha] with x hx
    change (2 : ℝ) • φ.grad (translateCoefficient (-z) a) (x + z) = 2 • φ.grad a x
    rw [hx]
  let T := inverseTranslatedFluxCorrector (scaledAKMCorrector φ 2) S z
    (measurePreserving_actualCoefficientTranslation Q (-z)) hc
  have h := hest (actualCoefficientLaw Q) (lawHypotheses_actualCoefficientLaw Q)
    ((2 : ℝ) • halfDirection i) (euclideanNorm_two_smul_halfDirection i)
    (scaledAKMCorrector φ 2) T r hr
  let f : Coefficient 2 (AKMUpperEllipticity L) → ENNReal := fun a =>
    ENNReal.ofReal ((Real.sqrt (⨍ x in ball 0 r,
      frobeniusNorm (T.potential a x -
        fluxHeatAverage (T.potential a) 0 r) ^ 2 ∂volume)) ^ p)
  change (∫⁻ a, f a ∂actualCoefficientLaw Q) ≤ _ at h
  rw [← lintegral_actualCoefficientTranslation Q z f] at h
  have hpoint (a : Coefficient 2 (AKMUpperEllipticity L)) :
      f (translateCoefficient z a) = ENNReal.ofReal
        ((Real.sqrt (⨍ x in ball z r,
          frobeniusNorm (S.potential a x -
            fluxHeatAverage (S.potential a) z r) ^ 2 ∂volume)) ^ p) := by
    dsimp [f, T, inverseTranslatedFluxCorrector]
    rw [translateCoefficient_add, neg_add_cancel, translateCoefficient_zero]
    rw [← flux_ball_heat_oscillation_translate]
  simpa only [hpoint] using h

end EinsteinRelation.Correctors
