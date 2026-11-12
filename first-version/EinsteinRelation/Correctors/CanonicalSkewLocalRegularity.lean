import EinsteinRelation.Correctors.CanonicalFluxPoissonData
import EinsteinRelation.Correctors.CanonicalRegularFlux
import EinsteinRelation.Correctors.HolderCurlSource
import EinsteinRelation.Correctors.PoissonContinuityAllScales

/-! Source: `paper/main.tex:741-753,762-766`. The actual canonical
heat-selected skew potential has continuous local versions, by its Poisson
equation with the regular canonical flux as divergence source. -/

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger HeatSelectedSkewMeaning
open ReductionImageV3 ActualImageLpStateTransport

/-- Continuous local versions of every entry on a common full-measure
event. No measurability or continuity of the supplied potential is assumed. -/
theorem ae_heatSelectedSkewCorrector_continuousOn_representatives
    (h68 : FluxGradientEstimate) (hP : BallPoincareEstimate)
    (h836 : InteriorRegularRepresentative)
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (σ : FieldPair d → Vec d → Mat d)
    (hσ : HasHeatSelectedSkewCorrectorColumn (Fact.out : 2 ≤ d) Q i σ) :
    ∀ᵐ ω ∂reducedEnvironmentLaw Q, ∀ j k : Fin d, ∀ n : ℕ,
      ∃ v : Vec d → ℝ, ContinuousOn v (Metric.ball 0 ((n : ℝ) + 1)) ∧
        (fun x => σ ω x j k) =ᵐ[volume.restrict (Metric.ball 0 ((n : ℝ) + 1))] v := by
  obtain ⟨F, hF⟩ := ae_canonicalFlux_Poisson_data h68 hP Q i σ hσ
  have hc := (measurePreserving_physicalReduction Q).quasiMeasurePreserving.ae
    (ae_canonicalRegularCenteredFlux hP h836 Q i)
  have hphys : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ j k : Fin d, ∀ n : ℕ,
      ∃ v : Vec d → ℝ, ContinuousOn v (Metric.ball 0 ((n : ℝ) + 1)) ∧
        (fun x => σ (reduce ω.1) x j k) =ᵐ[
          volume.restrict (Metric.ball 0 ((n : ℝ) + 1))] v := by
    filter_upwards [hF, hc] with ω hω hcω
    intro j k n
    let A : Vec d → Vec d := fun x =>
      canonicalRegularCenteredFlux Q i (reduce ω.1) x j • unitVector k -
      canonicalRegularCenteredFlux Q i (reduce ω.1) x k • unitVector j
    have hAc : Continuous A :=
      (((continuous_apply j).comp hcω.1).smul continuous_const).sub
        (((continuous_apply k).comp hcω.1).smul continuous_const)
    have hAm : Measurable A := hAc.measurable
    have hAH : ∀ R : ℝ, 0 < R → ∃ K : ℝ, ∀ l,
        HolderBound (ball 0 R) (1 / 2) (fun x => A x l) K := by
      intro R hR
      obtain ⟨K, hK⟩ := hcω.2.2 R hR
      obtain ⟨C, hC⟩ := exists_holderBound_curlSource (ball 0 R)
        (canonicalRegularCenteredFlux Q i (reduce ω.1)) (1 / 2) K hK
      exact ⟨C, hC j k⟩
    have hJ : HasWeakDivergence Set.univ
        (fun x => (fun l => F (translate x (reduce ω.1)) j k l) - A x) (fun _ => 0) := by
      apply (hω j k).2.1.congr_ae ?_ (ae_eq_refl _)
      simp only [Measure.restrict_univ]
      filter_upwards [hcω.2.1] with x hx
      rw [hx]
    let S : ℝ := ((d : ℝ) + 1) * ((n : ℝ) + 1)
    obtain ⟨v, hv, heq⟩ := exists_continuousOn_poisson_potential_ball_of_gt
      h836 (Fact.out : 2 ≤ d) (fun x => σ (reduce ω.1) x j k)
      (fun x l => F (translate x (reduce ω.1)) j k l) A
      (hω j k).1 hJ hAm (fun R hR => ((hω j k).2.2 R hR).1)
      (fun R hR => ((hω j k).2.2 R hR).2) hAH S (by dsimp [S]; positivity)
    exact ⟨v, hv.mono supBall_subset_dimension_euclideanBall,
      heq.filter_mono (ae_mono (Measure.restrict_mono_set volume
        supBall_subset_dimension_euclideanBall))⟩
  rw [← (measurePreserving_physicalReduction Q).map_eq]
  exact ((actualImageMeasurableEmbedding.comp measurableEmbedding_reducePhysical).ae_map_iff).mpr hphys

end EinsteinRelation.Correctors
