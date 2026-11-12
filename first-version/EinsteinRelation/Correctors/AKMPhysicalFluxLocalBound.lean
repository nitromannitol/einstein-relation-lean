import EinsteinRelation.Correctors.CanonicalFluxLocalBound
import EinsteinRelation.Correctors.AKMPhysicalFluxGaugeIdentification
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger HeatSelectedSkewMeaning
open Environment.AKMTestIntegralSupport ReductionImageV3
/-- Source: `paper/main.tex:733-745`. Entrywise gauge identification
transfers the canonical local Poisson estimate to the actual raw tensor. -/
theorem ae_physicalAKMFlux_local_bound_of_literature
    (h817 : LocalBoundednessEstimate) (h68 : FluxGradientEstimate)
    (hP : BallPoincareEstimate) (d : ℕ) [Fact (2 ≤ d)] :
    ∃ C : ℝ, 0 < C ∧ ∀ {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀)
      (i : Fin d) (φ : Corrector (actualCoefficientLaw Q) (halfDirection i))
      (S : FluxCorrector (scaledAKMCorrector φ 2)),
      (∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
        centeredFlux (scaledAKMCorrector φ 2)
          (project (r₀ := r₀) Q.ellipticity_parameter ω) y =
            ellipticityScale L •
              ((canonicalCorrectorFlux Q i (translate (r₀ • y) (reduce ω.1))).ofLp -
                (expectedCorrectorFlux Q i).ofLp)) →
      ∀ (σ : FieldPair d → Vec d → Mat d),
        HasHeatSelectedSkewCorrectorColumn (Fact.out : 2 ≤ d) Q i σ →
        ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ (j k : Fin d) (z : Vec d) (c M : ℝ),
          0 < M →
          (∀ᵐ x ∂volume.restrict (ball z 1), euclideanNorm
            ((canonicalCorrectorFlux Q i (translate x (reduce ω.1)) -
              expectedCorrectorFlux Q i).ofLp) ≤ M) →
          ∀ᵐ x ∂volume.restrict (ball z (1 / 4)),
            |(r₀ / ellipticityScale L) * S.potential
              (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x) j k - c| ≤
            C * (Real.sqrt (∫ x in ball z 1,
              |(r₀ / ellipticityScale L) * S.potential
                (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x) j k - c| ^ 2
                ∂volume) + M) := by
  obtain ⟨C, hC, hlocal⟩ := ae_canonicalFlux_local_bound_of_literature h817 h68 hP d
  refine ⟨C, hC, ?_⟩
  intro L r₀ Q i φ S hsource σ hσ
  have hgauge := ae_physicalAKMFlux_potential_gauge Q i φ S hsource σ hσ
  filter_upwards [hgauge, hlocal Q i σ hσ] with ω hg hl
  intro j k z c M hM hMb
  obtain ⟨b, hb⟩ := hg j k
  have heq : (fun x => σ (reduce ω.1) x j k - (c - b)) =ᵐ[volume]
      (fun x => (r₀ / ellipticityScale L) * S.potential
        (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x) j k - c) := by
    filter_upwards [hb] with x hx
    linarith
  have hI : (∫ x in ball z 1, |σ (reduce ω.1) x j k - (c - b)| ^ 2 ∂volume) =
      ∫ x in ball z 1, |(r₀ / ellipticityScale L) * S.potential
        (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x) j k - c| ^ 2 ∂volume := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae heq] with x hx
    rw [hx]
  have h := hl j k z (c - b) M hM hMb
  rw [hI] at h
  filter_upwards [h, ae_restrict_of_ae heq] with x hx he
  rwa [he] at hx
end EinsteinRelation.Correctors
