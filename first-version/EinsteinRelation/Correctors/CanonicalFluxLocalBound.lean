import EinsteinRelation.Correctors.CanonicalFluxPoissonData
import EinsteinRelation.Correctors.CanonicalCenteredFluxBound
import EinsteinRelation.Correctors.CurlSourceNormBound
import EinsteinRelation.Correctors.PoissonAllCenters
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger HeatSelectedSkewMeaning
open Environment.AKMTestIntegralSupport ReductionImageV3
/-- Source: `paper/main.tex:733-745`. The local Poisson estimate applies
to every canonical heat-selected tensor, at every center and in every gauge. -/
theorem ae_canonicalFlux_local_bound_of_literature
    (h817 : LocalBoundednessEstimate) (h68 : FluxGradientEstimate)
    (hP : BallPoincareEstimate) (d : ℕ) [Fact (2 ≤ d)] :
    ∃ C : ℝ, 0 < C ∧ ∀ {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀)
      (i : Fin d) (σ : FieldPair d → Vec d → Mat d),
      HasHeatSelectedSkewCorrectorColumn (Fact.out : 2 ≤ d) Q i σ →
      ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ (j k : Fin d) (z : Vec d) (c M : ℝ),
        0 < M →
        (∀ᵐ x ∂volume.restrict (ball z 1), euclideanNorm
          ((canonicalCorrectorFlux Q i (translate x (reduce ω.1)) -
            expectedCorrectorFlux Q i).ofLp) ≤ M) →
        ∀ᵐ x ∂volume.restrict (ball z (1 / 4)),
          |σ (reduce ω.1) x j k - c| ≤ C * (Real.sqrt
            (∫ x in ball z 1, |σ (reduce ω.1) x j k - c| ^ 2 ∂volume) + M) := by
  obtain ⟨C, hC, hlocal⟩ := poisson_local_bound_at_center_of_GT
    h817 d (Fact.out : 2 ≤ d)
  refine ⟨2 * C, by positivity, ?_⟩
  intro L r₀ Q i σ hσ
  obtain ⟨F, hF⟩ := ae_canonicalFlux_Poisson_data h68 hP Q i σ hσ
  filter_upwards [hF] with ω hw
  intro j k z c M hM hMb
  let G : Vec d → Vec d := fun x =>
    (canonicalCorrectorFlux Q i (translate x (reduce ω.1)) - expectedCorrectorFlux Q i).ofLp
  have hG : Measurable G := (canonical_flux_source_measurable_memLp Q i).1.comp
    (Probability.continuous_translate.measurable.comp
      (measurable_id.prodMk measurable_const))
  have hcurl : Measurable (fun x => G x j • unitVector k - G x k • unitVector j) :=
    ((measurable_pi_apply j).comp hG).smul_const _ |>.sub
      (((measurable_pi_apply k).comp hG).smul_const _)
  have hsource : ∀ᵐ x ∂volume.restrict (ball z 1),
      euclideanNorm (G x j • unitVector k - G x k • unitVector j) ≤ 2 * M := by
    filter_upwards [hMb] with x hx
    exact (euclideanNorm_curlSource_le (G x) j k).trans (by linarith)
  have hb := hlocal (fun x => σ (reduce ω.1) x j k)
    (fun x l => F (translate x (reduce ω.1)) j k l)
    (fun x => G x j • unitVector k - G x k • unitVector j)
    (hw j k).1 (hw j k).2.1 hcurl
    (fun R hR => ((hw j k).2.2 R hR).1)
    (fun R hR => ((hw j k).2.2 R hR).2) z c (2 * M) (by positivity) hsource
  filter_upwards [hb] with x hx
  have hs := Real.sqrt_nonneg
    (∫ x in ball z 1, |σ (reduce ω.1) x j k - c| ^ 2 ∂volume)
  nlinarith
end EinsteinRelation.Correctors
