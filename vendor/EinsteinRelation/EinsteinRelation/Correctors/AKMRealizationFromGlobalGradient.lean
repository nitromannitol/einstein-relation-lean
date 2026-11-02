import EinsteinRelation.Correctors.AKMHeatIntegrability

/-!
# AKM realization from a single global spatial identification

Source: `paper/main.tex:693-702,727-729`. Once a source corrector is
identified with the canonical gradient in all of space, the local
rescaling, expected-flux center, and Gaussian integrability follow.
Existence of that corrector and its identification remain internal
obligations; no uniqueness or domain-membership premise is hidden here.
-/

open MeasureTheory

noncomputable section

namespace EinsteinRelation.Correctors

open External.AKM Environment.AKMTestIntegralSupport ReductionImageV3

/-- The full AKM spatial-realization interface follows from the global
gradient identity, without separate center or integrability hypotheses. -/
def canonicalAKMSpatialRealization_of_global_gradient_identification
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (halfDirection i))
    (hid : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
      (2 : ℝ) • (halfDirection i + φ.grad (project (r₀ := r₀) Q.ellipticity_parameter ω) y) =
        (correctorUnitVector i + (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (translate (r₀ • y) (reduce ω.1))).ofLp) :
    CanonicalAKMSpatialRealization Q i where
  corrector := φ
  gradient_identification := by
    have hr : r₀ ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one Q.range_parameter)
    filter_upwards [hid] with ω hω
    have h := (Measure.quasiMeasurePreserving_smul (volume : Measure (Vec d))
      (inv_ne_zero hr)).ae hω
    have hs : ∀ᵐ x ∂(volume : Measure (Vec d)),
        (2 : ℝ) • (halfDirection i +
          φ.grad (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x)) =
        (correctorUnitVector i + (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (translate x (reduce ω.1))).ofLp := by
      simpa only [smul_smul, mul_inv_cancel₀ hr, one_smul] using h
    exact ae_restrict_of_ae hs
  mean_flux_identity := akm_meanFlux_halfDirection_of_global_gradient_identification Q i φ hid
  heat_integrable := akm_heat_integrable_of_global_gradient_identification Q i φ hid

end EinsteinRelation.Correctors

