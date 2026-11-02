import EinsteinFull.Calculus.ComplexForceSemigroupSupport
import EinsteinFull.Calculus.ComplexTransposeResolventSupport
import EinsteinFull.Frozen.StructuralData
import EinsteinFull.Frozen.SmoothEnvironment
import EinsteinRelation.Diffusion.Basic

open MeasureTheory Filter
open scoped NNReal Topology

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Smooth-scope version `V2` of `node_e_u3A_generators_u23_real_u2D_semigroupStmt`
(`e:generators#real-semigroup`, `paper/main.tex:242–250`). Same text as V1 with the roots'
placement of the structural data: `Q : EnvironmentLaw d D.ellipticity D.dependenceRange` and
`HasSmoothBounds D Q` (Assumption 1.2), then the real force `lam`. All five conjuncts are verbatim:
the canonical real-force evolution and its bilinear transpose have the frozen generator graphs, and the
forward evolution agrees with the actual reduced diffusion for every solution of the martingale
problem. -/
def node_e_u3A_generators_u23_real_u2D_semigroupStmtV2 : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
    HasSmoothBounds D Q →
    ∀ (lam : ℝ),
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
