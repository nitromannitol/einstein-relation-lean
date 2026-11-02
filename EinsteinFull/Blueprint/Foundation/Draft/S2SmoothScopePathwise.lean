import EinsteinFull.Frozen.EnvironmentLaw
import EinsteinFull.Frozen.StructuralData
import EinsteinFull.Frozen.SmoothEnvironment
import EinsteinRelation.Diffusion.Basic
import EinsteinRelation.Diffusion.ClockInverseSupport

open MeasureTheory
open scoped NNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Smooth-scope version `V2` of `node_eq_u2E_reduced_u2D_generator_u23_pathwiseStmt`
(`eq.reduced-generator#pathwise`, `paper/main.tex:222–227`). The text is that of the V1 node with the
roots' placement of the structural data: the law `Q` has the type
`EnvironmentLaw d D.ellipticity D.dependenceRange` and carries `HasSmoothBounds D Q` (Assumption 1.2),
exactly as in every numbered statement that mentions the diffusion; `Λ₀ := D.ellipticity`. Every
other quantifier and conclusion is verbatim: the force coordinate and the signed real force, the
"for all solutions" clause, the literal clock map, and the simultaneous-in-time identity on the same
path. -/
def node_eq_u2E_reduced_u2D_generator_u23_pathwiseStmtV2 : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
    HasSmoothBounds D Q →
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
      ∀ᵐ ω ∂Q.measure, ∀ hω : IsRegular D.ellipticity ω,
        PX (0, ω) = Measure.map
          (fun γ : Path d => Clock.InverseMeaningV3.inverseClockPath ω γ D.ellipticity hω)
          (PY (0, ω)) ∧
        ∀ᵐ γ ∂PY (0, ω), ∀ t : ℝ≥0,
          Clock.InverseMeaningV3.inverseClockPath ω γ D.ellipticity hω
            (Clock.physicalPathClock ω γ t) = γ t

end EinsteinFull.Blueprint
