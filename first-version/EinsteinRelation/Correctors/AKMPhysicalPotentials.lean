import EinsteinRelation.Correctors.AKMPhysicalFluxSobolev
import EinsteinRelation.Correctors.AKMPhysicalScalarSobolev
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport ReductionImageV3
/-- Source: `paper/main.tex:716-723`. The scalar potential in physical
coordinates, including the half-direction amplitude. -/
noncomputable abbrev physicalAKMScalarPotential {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) {i : Fin d}
    (φ : Corrector (actualCoefficientLaw Q) (halfDirection i)) : PhysicalField d L → Vec d → ℝ :=
  fun ω x => (2 * r₀) * φ.potential
    (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x)
/-- Source: `paper/main.tex:733-745`. The tensor potential in physical
coordinates with the canonical centered-flux amplitude. -/
noncomputable abbrev physicalAKMFluxPotential {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) {i : Fin d}
    (φ : Corrector (actualCoefficientLaw Q) (halfDirection i))
    (S : FluxCorrector (scaledAKMCorrector φ 2)) : PhysicalField d L → Vec d → Mat d :=
  fun ω x => (r₀ / ellipticityScale L) • S.potential
    (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x)
/-- Source: `paper/main.tex:716-723`. The actual samplewise identification
of the AKM gradient with the canonical physical gradient. -/
abbrev CanonicalAKMGradientIdentification {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (halfDirection i)) : Prop :=
  ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
    (2 : ℝ) • (halfDirection i + φ.grad
      (project (r₀ := r₀) Q.ellipticity_parameter ω) y) =
    (correctorUnitVector i + (canonicalCorrectorGradient Q i :
      Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
        (translate (r₀ • y) (reduce ω.1))).ofLp
end EinsteinRelation.Correctors
