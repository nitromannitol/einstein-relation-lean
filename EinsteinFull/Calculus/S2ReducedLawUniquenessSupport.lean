import EinsteinFull.Calculus.S2ClockLeftInverseSupport
import EinsteinFull.Blueprint.Foundation.node_eq_u2E_reduced_u2D_generator_u23_pathwise

/-!
# Uniqueness of the reduced origin law from the pathwise time-change relation

Two reduced solutions have the same inverse-clock image as a common physical solution, and
the inverse-clock path map has a measurable left inverse; hence the reduced origin laws
agree for almost every environment.
-/

open MeasureTheory
open scoped NNReal

noncomputable section
namespace EinsteinFull
open EinsteinRelation

/-- Same inverse-clock image of the origin laws, for a.e. environment, forces equal origin laws. -/
theorem originLaw_ae_eq_of_inverseClock {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (PX Y Y' : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure, ∀ hω : IsRegular Λ₀ ω, PX (0, ω) =
      Measure.map (fun γ : Path d => Clock.InverseMeaningV3.inverseClockPath ω γ Λ₀ hω)
        (Y (0, ω)))
    (hY' : ∀ᵐ ω ∂Q.measure, ∀ hω : IsRegular Λ₀ ω, PX (0, ω) =
      Measure.map (fun γ : Path d => Clock.InverseMeaningV3.inverseClockPath ω γ Λ₀ hω)
        (Y' (0, ω))) :
    ∀ᵐ ω ∂Q.measure, Y (0, ω) = Y' (0, ω) := by
  filter_upwards [hY, hY', Q.regular] with ω h1 h2 hreg
  exact pathLaw_eq_of_inverseClock_map_eq ω Λ₀ hreg _ _ ((h1 hreg).symm.trans (h2 hreg))

/-- The pathwise time-change relation of `node_eq_u2E_reduced_u2D_generator_u23_pathwiseStmt`
for one environment law `Q`, at every force coordinate and signed force. -/
def PathwiseAt {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) : Prop :=
  ∀ (i : Fin d) (lam : ℝ),
    (∃ PX PY : QuenchedPathLaws d,
      (∀ᵐ ω ∂Q.measure,
        SolvesMartingaleProblem (physicalGenerator i ω lam) 0 (PX (0, ω))) ∧
      (∀ᵐ ω ∂Q.measure,
        SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (PY (0, ω)))) ∧
    ∀ PX PY : QuenchedPathLaws d,
      (∀ᵐ ω ∂Q.measure,
        SolvesMartingaleProblem (physicalGenerator i ω lam) 0 (PX (0, ω))) →
      (∀ᵐ ω ∂Q.measure,
        SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (PY (0, ω))) →
      ∀ᵐ ω ∂Q.measure, ∀ hω : IsRegular Λ₀ ω,
        PX (0, ω) = Measure.map
          (fun γ : Path d => Clock.InverseMeaningV3.inverseClockPath ω γ Λ₀ hω)
          (PY (0, ω)) ∧
        ∀ᵐ γ ∂PY (0, ω), ∀ t : ℝ≥0,
          Clock.InverseMeaningV3.inverseClockPath ω γ Λ₀ hω
            (Clock.physicalPathClock ω γ t) = γ t

/-- The pathwise time-change node holds at every environment law. -/
theorem pathwiseAt_of_pathwise
    (hpath : Blueprint.node_eq_u2E_reduced_u2D_generator_u23_pathwiseStmt)
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} : PathwiseAt Q :=
  hpath d hd Λ₀ r₀ Q

/-- Any two reduced solutions have the same origin quenched law, for a.e. environment,
given the pathwise time-change relation at `Q`. -/
theorem reducedOriginLaw_ae_unique_of_pathwise
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q) (i : Fin d) (lam : ℝ)
    (Y Y' : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (Y (0, ω)))
    (hY' : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem (reducedGenerator i ω lam) 0
      (Y' (0, ω))) :
    ∀ᵐ ω ∂Q.measure, Y (0, ω) = Y' (0, ω) := by
  obtain ⟨⟨PX, PY, hPX, _⟩, huniq⟩ := hpath i lam
  have h1 := huniq PX Y hPX hY
  have h2 := huniq PX Y' hPX hY'
  refine originLaw_ae_eq_of_inverseClock Q PX Y Y' ?_ ?_
  · filter_upwards [h1] with ω h hω
    exact (h hω).1
  · filter_upwards [h2] with ω h hω
    exact (h hω).1

end EinsteinFull
