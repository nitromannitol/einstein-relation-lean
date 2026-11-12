import EinsteinRelation.Correctors.AKMCarrierIdentificationCoefficients
import EinsteinRelation.Environment.CountableLocallyIntegrableTests

open MeasureTheory
namespace EinsteinRelation.Correctors
open Environment.AKMTestIntegralSupport

/-- A measurable continuous reconstruction agreeing on continuous raw coefficients
agrees with the actual coefficient law up to spatial null sets. The countable
observation family is constructed internally (`paper/main.tex:699–708`, AKM (0.11)). -/
theorem ae_akm_field_eq_reconstruction {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀)
    (R : Coefficient d (AKMUpperEllipticity L) → CoefficientField d) (hR : Measurable R)
    (hReq : ∀ (a : Coefficient d (AKMUpperEllipticity L)) (ha : Continuous a.field),
      R a = ⟨a.field, ha⟩) :
    ∀ᵐ a ∂actualCoefficientLaw Q, a.field =ᵐ[volume] (R a : Vec d → Mat d) := by
  obtain ⟨T, hT⟩ := exists_countable_locally_integrable_determining_tests d
  exact ae_akm_field_eq_reconstruction_of_determining_tests Q R hR hReq T hT

end EinsteinRelation.Correctors
