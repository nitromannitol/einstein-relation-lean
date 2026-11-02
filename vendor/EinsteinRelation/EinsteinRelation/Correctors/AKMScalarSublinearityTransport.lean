import EinsteinRelation.Correctors.AKMFluxIdentification
import EinsteinRelation.Correctors.ScalarOrbitIntegerSublinearity
import EinsteinRelation.Correctors.SpatialIntegerPropertiesPushforward

/-!
# Scalar integer sublinearity on the raw law

Source: `paper/main.tex:693-698`. Only the countable sequence of scalar
spatial averages is transported through the measurable coefficient map.
-/
open MeasureTheory Filter Topology
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport ReductionImageV3

/-- A scalar coefficient-factor orbit inherits the proved integer-cube
sublinearity of its actual stationary L² representative. -/
theorem ae_akm_scalar_integerCube_sublinearity {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (f : Lp ℝ 2 (reducedEnvironmentLaw Q))
    (u : Coefficient d (AKMUpperEllipticity L) → Vec d → ℝ)
    (hu : Measurable (fun p : Coefficient d (AKMUpperEllipticity L) × Vec d => u p.1 p.2))
    (hid : ∀ᵐ ω ∂physicalReferenceLaw Q, (fun x =>
      u (project (r₀ := r₀) Q.ellipticity_parameter ω) x) =ᵐ[volume]
        (fun x => f (translate x (reduce ω.1)))) :
    ∀ᵐ a ∂actualCoefficientLaw Q, Tendsto (fun k : ℕ => (((k : ℝ) + 1)^2)⁻¹ *
      (⨍ x in Metric.closedBall (0 : Vec d) ((k : ℝ) + 1), |u a x|^2 ∂volume))
      atTop (𝓝 0) := by
  have hs := (measurePreserving_physicalReduction Q).quasiMeasurePreserving.ae
    (ae_scalar_orbit_integer_scaled_mean_square_zero (reducedEnvironmentLaw Q)
      (reducedEnvironmentLaw_stationary Q) f)
  apply ae_scalar_integerCube_sublinearity_of_pullback (physicalReferenceLaw Q)
    (project (r₀ := r₀) Q.ellipticity_parameter) (measurable_project Q.ellipticity_parameter) u hu
  filter_upwards [hs, hid] with ω hω hi
  apply hω.congr'
  apply Eventually.of_forall
  intro k
  have he : (⨍ x in Metric.closedBall (0 : Vec d) ((k : ℝ) + 1),
      |f (translate x (reduce ω.1))|^2 ∂volume) =
      ⨍ x in Metric.closedBall (0 : Vec d) ((k : ℝ) + 1),
        |u (project (r₀ := r₀) Q.ellipticity_parameter ω) x|^2 ∂volume := by
    apply average_congr
    filter_upwards [ae_restrict_of_ae hi] with x hx
    rw [hx]
  exact congrArg (fun t : ℝ => (((k : ℝ) + 1)^2)⁻¹ * t) he

end EinsteinRelation.Correctors
