import EinsteinRelation.Correctors.CanonicalFluxLocalSobolev
import EinsteinRelation.Correctors.CanonicalHarmonicFromPoincare
import EinsteinRelation.Correctors.CurlPoissonDivergence

/-! Source: `paper/main.tex:733-745`. The canonical heat-selected
tensor potential supplies the actual scalar Poisson equation and its
local Sobolev data on one common event. -/
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM HeatSelectedSkewMeaning
open Environment.AKMTestIntegralSupport ReductionImageV3

/-- The local integrability in the canonical flux divergence theorem also
applies after subtracting the expected column. -/
theorem ae_canonicalCenteredFlux_locallyIntegrable
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    ∀ᵐ ρ ∂reducedEnvironmentLaw Q, ∀ j : Fin d,
      LocallyIntegrable (fun x => (canonicalCorrectorFlux Q i (translate x ρ) -
        expectedCorrectorFlux Q i).ofLp j) volume := by
  filter_upwards [ae_canonicalCorrectorFlux_hasWeakDivergence Q i] with ρ hρ
  intro j
  exact (locallyIntegrableOn_univ.mp (hρ.1 j)).sub
    (locallyIntegrable_const _)

/-- The actual canonical family satisfies the divergence form used by
the local Poisson bound, without any additional integrability, regularity
or potential-identification hypothesis. -/
theorem ae_canonicalFlux_Poisson_data
    (h68 : FluxGradientEstimate)
    (hP : External.GilbargTrudinger.BallPoincareEstimate)
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀)
    (i : Fin d) (σ : FieldPair d → Vec d → Mat d)
    (hσ : HasHeatSelectedSkewCorrectorColumn (Fact.out : 2 ≤ d) Q i σ) :
    ∃ F : FieldPair d → Fin d → Fin d → Fin d → ℝ,
      ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ j k : Fin d,
        HasWeakGradient Set.univ (fun x => σ (reduce ω.1) x j k)
          (fun x l => F (translate x (reduce ω.1)) j k l) ∧
        HasWeakDivergence Set.univ
          (fun x => (fun l => F (translate x (reduce ω.1)) j k l) -
            ((canonicalCorrectorFlux Q i (translate x (reduce ω.1)) -
              expectedCorrectorFlux Q i).ofLp j • unitVector k -
             (canonicalCorrectorFlux Q i (translate x (reduce ω.1)) -
              expectedCorrectorFlux Q i).ofLp k • unitVector j)) (fun _ => 0) ∧
        ∀ R : ℝ, 0 < R →
          MemLp (fun x => σ (reduce ω.1) x j k) 2 (volume.restrict (ball 0 R)) ∧
          MemLp (fun x : Vec d => fun l : Fin d => F (translate x (reduce ω.1)) j k l)
            2 (volume.restrict (ball 0 R)) := by
  obtain ⟨F, hF, hlocal⟩ := ae_canonicalFlux_local_memLp h68 hP Q i σ hσ
  have hf := (measurePreserving_physicalReduction Q).quasiMeasurePreserving.ae hF
  have hG := (measurePreserving_physicalReduction Q).quasiMeasurePreserving.ae
    (ae_canonicalCenteredFlux_locallyIntegrable Q i)
  refine ⟨F, ?_⟩
  filter_upwards [hf, hG, hlocal] with ω hw hloc hl2
  intro j k
  refine ⟨hw.2 j k, ?_, hl2 j k⟩
  apply hasWeakDivergence_gradient_sub_curl_of_poisson j k (hw.2 j k) hloc
  intro ψ hψ hc
  exact (hw.1.2.2 ψ hψ hc j k).2.2.2

end EinsteinRelation.Correctors
