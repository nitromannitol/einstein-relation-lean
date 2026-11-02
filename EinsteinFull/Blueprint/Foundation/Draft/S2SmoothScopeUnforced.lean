import EinsteinFull.Frozen.ComplexEnvironmentSemigroup
import EinsteinFull.Frozen.ComplexTransposeSemigroup
import EinsteinFull.Frozen.StructuralData
import EinsteinFull.Frozen.SmoothEnvironment
import EinsteinRelation.Diffusion.Basic

open MeasureTheory
open scoped NNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Smooth-scope version `V2` of `node_stationary_u2D_environment_u23_unforced_u2D_processStmt`
(`stationary-environment#unforced-process`, `paper/main.tex:242`). Same text as V1 with the roots'
placement of the structural data: `Q : EnvironmentLaw d D.ellipticity D.dependenceRange` and
`HasSmoothBounds D Q` (Assumption 1.2). Every clause (semigroup on the actual reduced law, symmetry,
contraction and mean preservation, fixed space, zero horizontal energy, and the path clause for every
solution of the martingale problem) is verbatim. -/
def node_stationary_u2D_environment_u23_unforced_u2D_processStmtV2 : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
    HasSmoothBounds D Q →
    let i : Fin d := ⟨0, by omega⟩
    ∃ P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q i 0 P ∧
      IsComplexTransposeSemigroup Q P P ∧
      (∀ (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)),
        ‖P t f‖ ≤ ‖f‖ ∧
        (∫ ω, P t f ω ∂reducedLaw Q) = ∫ ω, f ω ∂reducedLaw Q) ∧
      (∀ f : Lp ℂ 2 (reducedLaw Q),
        (∀ t : ℝ≥0, P t f = f) ↔
          ∃ c : ℂ, f =ᵐ[reducedLaw Q] fun _ => c) ∧
      (∀ (f : Lp ℂ 2 (reducedLaw Q)) (G : Fin d → Lp ℂ 2 (reducedLaw Q)),
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G →
        (∫ ω, (∑ j : Fin d, ∑ k : Fin d,
          (ω.1 0 j k : ℂ) * G k ω * star (G j ω)).re ∂reducedLaw Q) = 0 →
        ∃ c : ℂ, f =ᵐ[reducedLaw Q] fun _ => c) ∧
      ∀ Y : QuenchedPathLaws d,
        (∀ᵐ ω ∂Q.measure,
          SolvesMartingaleProblem (reducedGenerator i ω 0) 0 (Y (0, ω))) →
        ∀ (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)), ∀ᵐ ω ∂Q.measure,
          Integrable (fun γ : Path d => f (translate (γ t) (reduce ω))) (Y (0, ω)) ∧
          P t f (reduce ω) =
            ∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂Y (0, ω)

end EinsteinFull.Blueprint
