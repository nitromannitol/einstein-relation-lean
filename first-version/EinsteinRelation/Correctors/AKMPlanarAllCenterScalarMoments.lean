import EinsteinRelation.Correctors.AKMTranslatedScalarCorrector
import EinsteinRelation.Correctors.AKMPlanarOscillationMoments
import EinsteinRelation.Correctors.HeatAverageTranslation

/-!
# Planar scalar L² moments at arbitrary centers

Source: `paper/main.tex:724-731`. The actual coefficient law is invariant
under real translations. Applying the origin estimate to the backwards
translated potential gives the estimate at any center, with the same
constant and with the heat center translated as well.
-/
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport ReductionImageV3

/-- The planar scalar estimate transports to every real center without
assuming stationarity of the chosen potential values. -/
theorem akm_planar_scalar_allCenter_L2_moments
    (h46 : ScalarPlanarL2Estimate) (L p : ℝ)
    (hK : 1 < AKMUpperEllipticity L) (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ {r₀ : ℝ} (Q : EnvironmentLaw 2 L r₀) (i : Fin 2)
      (φ : Corrector (actualCoefficientLaw Q) (halfDirection i)),
      (∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec 2)),
        (2 : ℝ) • (halfDirection i + φ.grad
          (project (r₀ := r₀) Q.ellipticity_parameter ω) y) =
          (correctorUnitVector i + (canonicalCorrectorGradient Q i :
            Lp (EuclideanSpace ℝ (Fin 2)) 2 (reducedEnvironmentLaw Q))
              (translate (r₀ • y) (reduce ω.1))).ofLp) →
      ∀ (z : Vec 2) (r : ℝ), 2 ≤ r →
      (∫⁻ a, ENNReal.ofReal ((Real.sqrt (⨍ x in ball z r,
        |φ.potential a x - scalarHeatAverage (φ.potential a) z r| ^ 2 ∂volume)) ^ p)
        ∂actualCoefficientLaw Q) ≤
        ENNReal.ofReal (C * (Real.sqrt (Real.log r)) ^ p) := by
  obtain ⟨C, hC, hest⟩ := akm_planar_scalar_L2_moments h46 (AKMUpperEllipticity L) p hK hp
  refine ⟨C, hC, ?_⟩
  intro r₀ Q i φ hid z r hr
  let ψ := inverseTranslatedScalarCorrector (by norm_num : 0 < 2) Q i φ hid z
  have h := hest (actualCoefficientLaw Q) (lawHypotheses_actualCoefficientLaw Q)
    (halfDirection i) (halfDirection_mem_ball i) ψ r hr
  let f : Coefficient 2 (AKMUpperEllipticity L) → ENNReal := fun a =>
    ENNReal.ofReal ((Real.sqrt (⨍ x in ball 0 r,
      |ψ.potential a x - scalarHeatAverage (ψ.potential a) 0 r| ^ 2 ∂volume)) ^ p)
  change (∫⁻ a, f a ∂actualCoefficientLaw Q) ≤ _ at h
  rw [← lintegral_actualCoefficientTranslation Q z f] at h
  have hpoint (a : Coefficient 2 (AKMUpperEllipticity L)) :
      f (translateCoefficient z a) = ENNReal.ofReal
        ((Real.sqrt (⨍ x in ball z r,
          |φ.potential a x - scalarHeatAverage (φ.potential a) z r| ^ 2 ∂volume)) ^ p) := by
    dsimp [f, ψ, inverseTranslatedScalarCorrector, correctorWithPotential]
    rw [translateCoefficient_add, neg_add_cancel, translateCoefficient_zero]
    rw [← scalar_ball_heat_oscillation_translate]
  simpa only [hpoint] using h

end EinsteinRelation.Correctors
