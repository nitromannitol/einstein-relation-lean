import EinsteinRelation.Correctors.AKMCarrierIdentificationCellFlux
import EinsteinRelation.Environment.AKMReconstructionAgreement

/-!
# The cell-flux field from the canonical gradient identity

Source: `paper/main.tex:693-702,727-729`. The raw coefficient equality is
proved using the common-test argument, so cell-flux integrability requires
no coefficient-identification or determining-test premise.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport ReductionImageV3

/-- Ordinary cell-flux integrability follows from joint measurability
and the global canonical-gradient identity alone. -/
theorem akm_cellFlux_integrable_of_canonical_gradient
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (g : Coefficient d (AKMUpperEllipticity L) → Vec d → Vec d)
    (hg : Measurable (fun p : Coefficient d (AKMUpperEllipticity L) × Vec d => g p.1 p.2))
    (hid : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
      (2 : ℝ) • (halfDirection i + g (project (r₀ := r₀) Q.ellipticity_parameter ω) y) =
        (correctorUnitVector i + (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (translate (r₀ • y) (reduce ω.1))).ofLp) :
    Integrable (fun a => ∫ x in unitCell d, (a x).mulVec (halfDirection i + g a x))
      (actualCoefficientLaw Q) := by
  obtain ⟨R, hR, hReq⟩ := exists_measurable_continuous_reconstruction
    (d := d) (K := AKMUpperEllipticity L)
  exact akm_cellFlux_integrable_of_global_identification Q i R hR
    (ae_actualCoefficientLaw_field_eq_reconstruction Q R hR hReq) g hg hid

end EinsteinRelation.Correctors
