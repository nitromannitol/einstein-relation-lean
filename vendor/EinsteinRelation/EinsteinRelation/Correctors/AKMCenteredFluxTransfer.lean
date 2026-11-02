import EinsteinRelation.Correctors.AKMFluxIdentification
import EinsteinRelation.Correctors.AKMSpatialFluxIdentification
import EinsteinRelation.External.AKMCorrectorOscillation

/-!
# Rescaling the centered AKM flux

Source: `paper/main.tex:697-702,716,733-739`. The actual source law uses
the coefficient multiplier `κ` and the half-direction. Subtracting the
identified expected flux therefore leaves the factor `κ/2`. No flux
corrector identification or regularity estimate is assumed.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport ReductionImageV3

/-- The literal centered source flux is the rescaled canonical centered
flux, with the deterministic coefficient and direction factors retained. -/
theorem ae_akmCenteredFlux_eq_scaled_canonicalCenteredFlux
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (halfDirection i))
    (hid : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
      (2 : ℝ) • (halfDirection i + φ.grad
        (project (r₀ := r₀) Q.ellipticity_parameter ω) y) =
      (correctorUnitVector i + (canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
          (translate (r₀ • y) (reduce ω.1))).ofLp) :
    ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
      centeredFlux φ (project (r₀ := r₀) Q.ellipticity_parameter ω) y =
        (ellipticityScale L / 2) •
          ((canonicalCorrectorFlux Q i (translate (r₀ • y) (reduce ω.1))).ofLp -
            (expectedCorrectorFlux Q i).ofLp) := by
  have hmean := akm_meanFlux_of_global_gradient_identification Q i φ hid
  have hflux := ae_akmFlux_eq_scaled_canonicalFlux Q i φ.grad hid
  filter_upwards [hflux] with ω hω
  filter_upwards [hω] with y hy
  simp only [centeredFlux, hy, hmean, smul_sub]

/-- Expressing the same centered flux in the physical coordinate cancels
the range dilation. -/
theorem ae_akmCenteredFlux_physical_coordinate
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (halfDirection i))
    (hid : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
      (2 : ℝ) • (halfDirection i + φ.grad
        (project (r₀ := r₀) Q.ellipticity_parameter ω) y) =
      (correctorUnitVector i + (canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
          (translate (r₀ • y) (reduce ω.1))).ofLp) :
    ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      centeredFlux φ (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x) =
        (ellipticityScale L / 2) •
          ((canonicalCorrectorFlux Q i (translate x (reduce ω.1))).ofLp -
            (expectedCorrectorFlux Q i).ofLp) := by
  have hr : 0 < r₀ := zero_lt_one.trans_le Q.range_parameter
  filter_upwards [ae_akmCenteredFlux_eq_scaled_canonicalCenteredFlux Q i φ hid]
    with ω hω
  have h := (Measure.quasiMeasurePreserving_smul (volume : Measure (Vec d))
    (inv_ne_zero hr.ne')).ae hω
  simpa only [smul_smul, mul_inv_cancel₀ hr.ne', one_smul] using h

end EinsteinRelation.Correctors
