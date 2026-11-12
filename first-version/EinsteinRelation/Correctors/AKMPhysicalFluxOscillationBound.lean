import EinsteinRelation.Correctors.AKMPhysicalAffineLocalBound
import EinsteinRelation.Correctors.AKMPhysicalFluxLocalBound
import EinsteinRelation.Correctors.CanonicalCenteredFluxBound
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger HeatSelectedSkewMeaning
open Environment.AKMTestIntegralSupport ReductionImageV3
/-- Source: `paper/main.tex:733-745`. The tensor local bound uses only
scalar and tensor local L² oscillations in any chosen common gauges. -/
theorem ae_physicalAKMFlux_local_bound_from_scalar_oscillation
    (h817 : LocalBoundednessEstimate) (h68 : FluxGradientEstimate)
    (hP : BallPoincareEstimate) (h832 : InteriorGradientEstimate)
    (h836 : InteriorRegularRepresentative) (d : ℕ) [Fact (2 ≤ d)]
    (L : ℝ) (hL : 1 ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∀ {r₀ : ℝ} (Q : EnvironmentLaw d L r₀)
      (i : Fin d) (φ : Corrector (actualCoefficientLaw Q) (halfDirection i))
      (S : FluxCorrector (scaledAKMCorrector φ 2)),
      (∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
        (2 : ℝ) • (halfDirection i + φ.grad
          (project (r₀ := r₀) Q.ellipticity_parameter ω) y) =
        (correctorUnitVector i + (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (translate (r₀ • y) (reduce ω.1))).ofLp) →
      (∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
        centeredFlux (scaledAKMCorrector φ 2)
          (project (r₀ := r₀) Q.ellipticity_parameter ω) y =
            ellipticityScale L •
              ((canonicalCorrectorFlux Q i (translate (r₀ • y) (reduce ω.1))).ofLp -
                (expectedCorrectorFlux Q i).ofLp)) →
      ∀ (σ : FieldPair d → Vec d → Mat d),
        HasHeatSelectedSkewCorrectorColumn (Fact.out : 2 ≤ d) Q i σ →
        ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ (j k : Fin d) (z : Vec d) (c b : ℝ),
          ∀ᵐ x ∂volume.restrict (ball z (1 / 4)),
            |(r₀ / ellipticityScale L) * S.potential
              (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x) j k - b| ≤
            C * (Real.sqrt (∫ x in ball z 1,
              |(r₀ / ellipticityScale L) * S.potential
                (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x) j k - b| ^ 2
                ∂volume) + 1 + Real.sqrt (∫ x in ball z 4,
                |(2 * r₀) * φ.potential
                  (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x) - c| ^ 2
                    ∂volume)) := by
  obtain ⟨A, hA, ha⟩ := ae_physicalAKMAffineGradient_local_bound_of_GT
    h817 h832 h836 d L hL
  obtain ⟨B, hB, hb⟩ := ae_physicalAKMFlux_local_bound_of_literature h817 h68 hP d
  let K := sourceReducedBound L
  have hK : 0 < K := by dsimp [K]; unfold sourceReducedBound; positivity
  refine ⟨B * (K * (A + 1) + 1), by positivity, ?_⟩
  intro r₀ Q i φ S hid hsource σ hσ
  have hf := (measurePreserving_physicalReduction Q).quasiMeasurePreserving.ae
    (ae_canonicalCenteredFlux_bound_of_affineBound Q i)
  filter_upwards [ha Q i φ hid, hb Q i φ S hsource σ hσ, hf] with ω hgrad hlocal hflux
  intro j k z c b
  let U := Real.sqrt (∫ x in ball z 4, |(2 * r₀) * φ.potential
    (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x) - c| ^ 2 ∂volume)
  have hU : 0 ≤ U := Real.sqrt_nonneg _
  let M := K * (A * (1 + U) + 1)
  have hM : 0 < M := by dsimp [M]; positivity
  have hsourceM := hflux (ball z 1) (A * (1 + U)) (hgrad z c)
  have h := hlocal j k z b M hM hsourceM
  filter_upwards [h] with x hx
  have hT : 0 ≤ Real.sqrt (∫ x in ball z 1,
    |(r₀ / ellipticityScale L) * S.potential
      (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x) j k - b| ^ 2 ∂volume) :=
    Real.sqrt_nonneg _
  have hcoeff : 0 ≤ K * (A + 1) := by positivity
  dsimp [M] at hx
  change _ ≤ B * (K * (A + 1) + 1) * (_ + 1 + U)
  nlinarith [mul_nonneg hcoeff hT, mul_nonneg hK.le hU]
end EinsteinRelation.Correctors
