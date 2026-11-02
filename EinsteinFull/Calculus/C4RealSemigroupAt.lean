import EinsteinFull.Blueprint.Foundation.Draft.S2SmoothScopeRealSemigroup

open MeasureTheory Filter
open scoped NNReal Topology

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- The five clauses of `e:generators#real-semigroup` at one environment law, for every
real force. The smooth-scope contract supplies them at each law with smooth bounds. -/
def RealSemigroupAt {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (Q : EnvironmentLaw d Λ r) : Prop :=
  ∀ lam : ℝ,
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

/-- The smooth-scope real-semigroup contract at one law with smooth bounds. -/
theorem realSemigroupAt_of_stmtV2
    (h : node_e_u3A_generators_u23_real_u2D_semigroupStmtV2)
    {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q) :
    RealSemigroupAt hd Q :=
  h d hd D Q hQ

end EinsteinFull.Blueprint
