import EinsteinRelation.Correctors.StationaryHeatGradientBound
import EinsteinRelation.Correctors.StationaryHeatSelectionRescaling

/-! Source: `paper/main.tex:722,756`. Real time cutoffs for the actual
canonical centered source require no additional literature premise. -/
open MeasureTheory Filter Topology
namespace EinsteinRelation.Correctors
open External.AKM HeatSelectedSkewMeaning

/-- The actual canonical source preserves every existing heat-selected
gradient under a fixed positive time dilation. The full-measure event is
chosen before the gradient, including gradients supplied on a larger
probability space. Both cutoffs vary independently. -/
theorem ae_canonical_flux_heat_selection_rescaled_local_L2
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (c : ℝ) (hc : 0 < c) :
    ∀ᵐ ω ∂reducedEnvironmentLaw Q, ∀ G : Fin d → Fin d → Vec d → Vec d,
      IsHeatSelectedFluxGradient
        (fun y => (canonicalCorrectorFlux Q i (translate y ω) -
          expectedCorrectorFlux Q i).ofLp) G →
      ∀ (j k l : Fin d) (R : ℕ),
        (∀ m n, MemLp
          (rescaledAKMHeatGradientTruncation
            (fun y => (canonicalCorrectorFlux Q i (translate y ω) -
              expectedCorrectorFlux Q i).ofLp) c m n j k l)
            2 (volume.restrict (ball 0 ((R : ℝ) + 1)))) ∧
        Tendsto (fun mn : ℕ × ℕ => eLpNorm
          (fun x => rescaledAKMHeatGradientTruncation
            (fun y => (canonicalCorrectorFlux Q i (translate y ω) -
              expectedCorrectorFlux Q i).ofLp) c mn.1 mn.2 j k l x - G j k x l)
            2 (volume.restrict (ball 0 ((R : ℝ) + 1)))) atTop (𝓝 0) := by
  let F : FieldPair d → Vec d := fun ω =>
    (canonicalCorrectorFlux Q i ω - expectedCorrectorFlux Q i).ofLp
  obtain ⟨hF, hF2⟩ := canonical_flux_source_measurable_memLp Q i
  obtain ⟨C, hC, hbound⟩ := exists_stationary_heatGradient_L2_bound
    (reducedEnvironmentLaw_stationary Q) F hF hF2
  exact ae_heat_selection_rescaled_local_L2 (reducedEnvironmentLaw Q)
    (reducedEnvironmentLaw_stationary Q) F hF C c hC hc hbound

end EinsteinRelation.Correctors
