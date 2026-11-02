import EinsteinFull.Calculus.ComplexForceSemigroupSupport
import EinsteinFull.Calculus.ComplexTransposeResolventSupport
import EinsteinRelation.Diffusion.Basic

open MeasureTheory Filter
open scoped NNReal Topology

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Node `e:generators#real-semigroup`, `paper/main.tex:242–250`.
The canonical real-force evolution and its bilinear transpose have exactly
the frozen full generator graphs. The forward evolution agrees with the
actual reduced diffusion, rather than an unrelated Markov family. No smooth
coefficient assumption or realization premise is inserted. -/
def node_e_u3A_generators_u23_real_u2D_semigroupStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ)
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ),
    let i : Fin d := ⟨0, by omega⟩
    let P := forcedComplexEvolution Q i (lam : ℂ)
    let Pdag := fun t => complexL2Transpose (reducedLaw Q) (P t)
    IsComplexEnvironmentSemigroup Q i (lam : ℂ) P ∧
    IsComplexTransposeSemigroup Q P Pdag ∧
    (∀ f : Lp ℂ 2 (reducedLaw Q), Continuous (fun t : ℝ≥0 => Pdag t f)) ∧
    (∀ f g : Lp ℂ 2 (reducedLaw Q),
      Tendsto (fun t : ℝ≥0 => ((t : ℝ) : ℂ)⁻¹ • (Pdag t f - f))
        (𝓝[>] (0 : ℝ≥0)) (𝓝 g) ↔ IsComplexTransposeGeneratorPair Q i (lam : ℂ) f g) ∧
    ∀ Y : QuenchedPathLaws d,
      (∀ᵐ ω ∂Q.measure,
        SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (Y (0, ω))) →
      ∀ (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)), ∀ᵐ ω ∂Q.measure,
        Integrable (fun γ : Path d => f (translate (γ t) (reduce ω))) (Y (0, ω)) ∧
        P t f (reduce ω) =
          ∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂Y (0, ω)

end EinsteinFull.Blueprint
