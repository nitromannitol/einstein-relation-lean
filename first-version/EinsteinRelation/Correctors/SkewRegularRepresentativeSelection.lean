import EinsteinRelation.Correctors.RegularRepresentativeSelection
import EinsteinRelation.Correctors.SkewRegularRepresentativeCongruence

/-! Source: `paper/main.tex:741-753,762-766`. The shrinking-average
selection preserves the actual heat-selected skew predicate. Local
Poisson regularity and a measurable initial gauge are separate obligations. -/

open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors
open HeatSelectedSkewMeaning

/-- Entrywise spatial averaging selects a tensor representative. -/
def skewRegularRepresentative {d : ℕ} (σ : FieldPair d → Vec d → Mat d)
    (ω : FieldPair d) (x : Vec d) : Mat d := fun j k =>
  spatialRegularRepresentative (fun ρ z => σ ρ z j k) ω x

/-- A jointly measurable tensor remains jointly measurable after selection. -/
theorem measurable_skewRegularRepresentative {d : ℕ}
    (σ : FieldPair d → Vec d → Mat d)
    (hσ : Measurable (fun p : Vec d × FieldPair d => σ p.2 p.1)) :
    Measurable (fun p : Vec d × FieldPair d => skewRegularRepresentative σ p.2 p.1) := by
  change @Measurable _ (Fin d → Fin d → ℝ) _ (borel _) _
  rw [← (Pi.borelSpace (X := fun _ : Fin d => Fin d → ℝ)).measurable_eq]
  apply measurable_pi_lambda
  intro j
  apply measurable_pi_lambda
  intro k
  exact measurable_spatialRegularRepresentative _
    ((show Continuous (fun A : Mat d => A j k) by fun_prop).measurable.comp hσ)

/-- Local continuous versions give a continuous tensor on one common
full-measure event, preserving its exact heat-selected source predicate. -/
theorem skewRegularRepresentative_preserves_heatSelectedSkewCorrector
    {d : ℕ} (hd : 2 ≤ d) {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (σ : FieldPair d → Vec d → Mat d)
    (hσ : HasHeatSelectedSkewCorrectorColumn hd Q i σ)
    (hloc : ∀ᵐ ω ∂reducedEnvironmentLaw Q, ∀ j k : Fin d, ∀ n : ℕ,
      ∃ v : Vec d → ℝ, ContinuousOn v (Metric.ball 0 ((n : ℝ) + 1)) ∧
        (fun x => σ ω x j k) =ᵐ[volume.restrict (Metric.ball 0 ((n : ℝ) + 1))] v) :
    HasHeatSelectedSkewCorrectorColumn hd Q i (skewRegularRepresentative σ) ∧
      (∀ᵐ ω ∂reducedEnvironmentLaw Q, Continuous (skewRegularRepresentative σ ω)) ∧
      ∀ᵐ ω ∂reducedEnvironmentLaw Q, σ ω =ᵐ[volume] skewRegularRepresentative σ ω := by
  have ha : ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      Continuous (skewRegularRepresentative σ ω) ∧
        σ ω =ᵐ[volume] skewRegularRepresentative σ ω := by
    filter_upwards [hloc] with ω hω
    have hj (j k : Fin d) := continuous_spatialRegularRepresentative_of_ball_versions
      (fun x => σ ω x j k) (hω j k)
    refine ⟨continuous_pi_iff.mpr (fun j =>
      continuous_pi_iff.mpr (fun k => (hj j k).1)), ?_⟩
    filter_upwards [ae_all_iff.mpr (fun j => ae_all_iff.mpr (fun k => (hj j k).2))]
      with x hx
    exact funext (fun j => funext (hx j))
  exact ⟨heatSelectedSkewCorrector_congr_spatial_ae hd Q i hσ (ha.mono (fun _ h => h.2)),
    ha.mono (fun _ h => h.1), ha.mono (fun _ h => h.2)⟩

end EinsteinRelation.Correctors
