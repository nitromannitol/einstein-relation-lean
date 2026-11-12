import EinsteinRelation.Correctors.AKMScalarGaugeProductionTransfer
import EinsteinRelation.Correctors.AKMUnitFluxConstruction
import EinsteinRelation.Correctors.StationaryFluxBallMoments

/-!
# Joint stationary scalar and flux representatives

Source: `paper/main.tex:724-731`. In dimension greater than two, AKM
(4.5) and (6.14) supply representatives on the same actual coefficient
law. Their radius-four L² moments are uniform in the center, and their
gradient and centered flux retain the canonical physical identification.
-/
open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport ReductionImageV3
open NormalizedScalarPhysicalLawTransportSupport
open NormalizedSpatialRepresentativeSupport

/-- The high-dimensional local L² source estimates can be realized
jointly, with one constant chosen before the environment law and index.
Both representatives are actual source correctors; in particular, the
flux representative retains the literal heat selection. -/
theorem exists_joint_stationary_akm_ball_four_moments
    (h45 : ScalarStationaryEstimate) (h68 : FluxGradientEstimate)
    (h614 : FluxStationaryEstimate)
    (hP : External.GilbargTrudinger.BallPoincareEstimate)
    (d : ℕ) [Fact (2 ≤ d)] (hd : 2 < d) (L r₀ p : ℝ)
    (hL : 1 ≤ L) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : EnvironmentLaw d L r₀) (i : Fin d),
      ∃ ψ : Corrector (actualCoefficientLaw Q) (halfDirection i),
        ∃ S : FluxCorrector (scaledAKMCorrector ψ 2),
          Measurable (fun q : Coefficient d (AKMUpperEllipticity L) × Vec d =>
            ψ.potential q.1 q.2) ∧
          ScalarStationary (actualCoefficientLaw Q) ψ.potential ∧
          (∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
            (2 : ℝ) • (halfDirection i + ψ.grad
              (project (r₀ := r₀) Q.ellipticity_parameter ω) y) =
            (correctorUnitVector i + (canonicalCorrectorGradient Q i :
              Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
                (translate (r₀ • y) (reduce ω.1))).ofLp) ∧
          (∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
            centeredFlux (scaledAKMCorrector ψ 2)
              (project (r₀ := r₀) Q.ellipticity_parameter ω) y =
              ellipticityScale L •
                ((canonicalCorrectorFlux Q i
                  (translate (r₀ • y) (reduce ω.1))).ofLp -
                    (expectedCorrectorFlux Q i).ofLp)) ∧
          (∀ j k, ScalarStationary (actualCoefficientLaw Q)
            (fun a x => S.potential a x j k)) ∧
          (∀ z : Vec d, (∫⁻ a, ENNReal.ofReal ((Real.sqrt
            (∫ x in ball z 4, |ψ.potential a x| ^ 2 ∂volume)) ^ p)
            ∂actualCoefficientLaw Q) ≤ ENNReal.ofReal C) ∧
          (∀ z : Vec d, (∫⁻ a, ENNReal.ofReal ((Real.sqrt
            (∫ x in ball z 4, frobeniusNorm (S.potential a x) ^ 2 ∂volume)) ^ p)
            ∂actualCoefficientLaw Q) ≤ ENNReal.ofReal C) ∧
          ∀ (ζ : SourceMollifier d) (R : ℝ) (hR : 1 ≤ R) (y : Point d)
            (φ : FieldPair d → Point d → ℝ),
            IsNormalizedCanonicalScalarCorrector Q i ζ R hR y φ →
            ∀ᵐ ω ∂physicalReferenceLaw Q, ∃ c : ℝ,
              (fun x : Vec d => φ (reduce ω.1) (WithLp.toLp 2 x)) =ᵐ[volume]
                (fun x => (2 * r₀) * ψ.potential
                  (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x) + c) := by
  have hp0 : 0 < p := by linarith
  have hK : 1 < AKMUpperEllipticity L := by
    have hexp : 1 < Real.exp (2 * L) := Real.one_lt_exp_iff.mpr (by linarith)
    have hκ : 1 < ellipticityScale L := by
      unfold ellipticityScale
      nlinarith
    unfold AKMUpperEllipticity
    nlinarith
  obtain ⟨Cφ, hCφ, hφest⟩ := akm_stationary_scalar_ball_four_moments
    h45 d hd (AKMUpperEllipticity L) p hK hp
  obtain ⟨Cσ, hCσ, hσest⟩ := akm_stationary_flux_ball_four_moments
    h614 d hd (AKMUpperEllipticity L) p hK hp
  obtain ⟨_, _, hflux⟩ := akm_flux_gradient_L2_moments h68 d
    (Fact.out : 2 ≤ d) (AKMUpperEllipticity L) p hK hp0
  refine ⟨Cφ + Cσ, by positivity, ?_⟩
  intro Q i
  obtain ⟨φ₀, hid₀⟩ := exists_akmCorrector_global_gradient_identification hP Q i
  obtain ⟨ψ, hm, hg, hs, hφb⟩ := hφest (actualCoefficientLaw Q)
    (lawHypotheses_actualCoefficientLaw Q) (halfDirection i)
    (halfDirection_mem_ball i) φ₀
  have hid : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
      (2 : ℝ) • (halfDirection i + ψ.grad
        (project (r₀ := r₀) Q.ellipticity_parameter ω) y) =
      (correctorUnitVector i + (canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
          (translate (r₀ • y) (reduce ω.1))).ofLp := by
    have hg' := (measurePreserving_akmProject Q).quasiMeasurePreserving.ae hg
    filter_upwards [hg', hid₀] with ω hω hiω
    filter_upwards [hω, hiω] with y hy hiy
    simpa only [hy] using hiy
  obtain ⟨⟨S₀⟩, _⟩ := hflux (actualCoefficientLaw Q)
    (lawHypotheses_actualCoefficientLaw Q) ((2 : ℝ) • halfDirection i)
    (euclideanNorm_two_smul_halfDirection i) (scaledAKMCorrector ψ 2)
  obtain ⟨S, _, hSs, _, hSb⟩ := hσest (actualCoefficientLaw Q)
    (lawHypotheses_actualCoefficientLaw Q) ((2 : ℝ) • halfDirection i)
    (euclideanNorm_two_smul_halfDirection i) (scaledAKMCorrector ψ 2) S₀
  refine ⟨ψ, S, hm, hs, hid,
    ae_unitAKMCenteredFlux_eq_scaled_canonicalCenteredFlux Q i ψ hid, hSs, ?_, ?_,
    akmPotential_gauge_identification_production Q i ψ hid⟩
  · intro z
    exact (hφb z).trans (ENNReal.ofReal_le_ofReal (by linarith))
  · intro z
    exact (hSb z).trans (ENNReal.ofReal_le_ofReal (by linarith))

end EinsteinRelation.Correctors
