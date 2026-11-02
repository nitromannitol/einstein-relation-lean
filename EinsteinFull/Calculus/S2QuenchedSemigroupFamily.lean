import EinsteinFull.Calculus.S2ReducedLawUniquenessSupport
import EinsteinFull.Calculus.S2UnforcedSemigroupSupport

/-!
# Identification of the quenched process with the environment semigroup, via one family

`QuenchedSemigroupFamilyStmt` asks for ONE reduced quenched path-law kernel `Y` (solving
the reduced martingale problem from the origin for a.e. environment) whose environment-seen-
from-the-particle expectations are the actual constructed `L²` evolution
`forcedComplexEvolution`. It is the natural output of constructing the process from the
semigroup (Feller construction). Combined with the uniqueness of the reduced origin law
(`reducedOriginLaw_ae_unique_of_pathwise`), it gives the identification for *every*
solution `Y'`.
-/

open MeasureTheory
open scoped NNReal

noncomputable section
namespace EinsteinFull
open EinsteinRelation

/-- One reduced quenched family realizing the actual complex `L²` evolution at real force. -/
def QuenchedSemigroupFamilyStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (Λ₀ r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) (lam : ℝ),
    ∃ Y : QuenchedPathLaws d,
      (∀ᵐ ω ∂Q.measure,
        SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (Y (0, ω))) ∧
      ∀ (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)), ∀ᵐ ω ∂Q.measure,
        Integrable (fun γ : Path d => f (translate (γ t) (reduce ω))) (Y (0, ω)) ∧
        forcedComplexEvolution Q i (lam : ℂ) t f (reduce ω) =
          ∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂Y (0, ω)

/-- The path clause of both nodes for an arbitrary reduced solution, from one realizing family
and the pathwise node. -/
theorem pathClause_of_family
    (hpath : Blueprint.node_eq_u2E_reduced_u2D_generator_u23_pathwiseStmt)
    (hfam : QuenchedSemigroupFamilyStmt)
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (lam : ℝ) :
    ∀ Y : QuenchedPathLaws d,
      (∀ᵐ ω ∂Q.measure,
        SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (Y (0, ω))) →
      ∀ (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)), ∀ᵐ ω ∂Q.measure,
        Integrable (fun γ : Path d => f (translate (γ t) (reduce ω))) (Y (0, ω)) ∧
        forcedComplexEvolution Q i (lam : ℂ) t f (reduce ω) =
          ∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂Y (0, ω) := by
  obtain ⟨Y0, hY0, hid⟩ := hfam d hd Λ₀ r₀ Q i lam
  intro Y hY t f
  have huniq := reducedOriginLaw_ae_unique_of_pathwise (hpath := pathwiseAt_of_pathwise hpath hd) Q i lam Y0 Y hY0 hY
  filter_upwards [huniq, hid t f] with ω he hω
  rw [← he]
  exact hω

end EinsteinFull
