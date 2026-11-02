import EinsteinFull.Frozen.ComplexEnvironmentSemigroup
import EinsteinFull.Frozen.ComplexTransposeSemigroup
import EinsteinRelation.Diffusion.Basic

open MeasureTheory
open scoped NNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Node `stationary-environment#unforced-process`, `paper/main.tex:242`.
The actual unforced environment process realizes the canonical horizontal
generator. Its semigroup is symmetric, preserves the reduced law and has
only constants in its fixed space. Zero horizontal Dirichlet energy forces
constancy, on the actual reduced joint coefficient carrier. No smoothness,
process realization, invariant law or ergodicity is supplied as a premise. -/
def node_stationary_u2D_environment_u23_unforced_u2D_processStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ)
    (Q : EnvironmentLaw d Λ₀ r₀),
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
