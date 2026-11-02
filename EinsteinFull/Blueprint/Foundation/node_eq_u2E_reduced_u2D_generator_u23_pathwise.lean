import EinsteinFull.Frozen.EnvironmentLaw
import EinsteinRelation.Diffusion.Basic
import EinsteinRelation.Diffusion.ClockInverseSupport

open MeasureTheory
open scoped NNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Graph node `eq.reduced-generator#pathwise`, `paper/main.tex:222–227`.
Existence of the actual real quenched diffusion laws and identification by the
literal clock map. The identity is simultaneous in time on the same path;
the clock is the frozen physical coefficient clock, not a freely chosen one.
No martingale-problem uniqueness or time-change input is assumed. Signed real
force is retained. The law predicates below are the defining martingale
problems, not a list of desired diffusion estimates. -/
def node_eq_u2E_reduced_u2D_generator_u23_pathwiseStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (Λ₀ r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) (lam : ℝ),
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

end EinsteinFull.Blueprint
