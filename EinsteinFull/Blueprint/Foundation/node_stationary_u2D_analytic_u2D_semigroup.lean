import EinsteinFull.Frozen.StructuralData
import EinsteinFull.Frozen.SmoothEnvironment
import EinsteinFull.Calculus.ComplexForceAnalyticSupport
import EinsteinFull.Calculus.ComplexTransposeSupport

open MeasureTheory Set
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Node `stationary-analytic-semigroup`, `paper/main.tex:250`, proof
`paper/main.tex:749–754` (also 614,1082,1193–1204).
The canonical stationary complex evolution and its bilinear transpose extend
the real generator graphs. Force holomorphy is in the actual stationary L2
and Lp carriers. Compact-disc/time bounds are uniform over the smooth law,
with their moment/disc/time parameters chosen first. Physical real-force
realization belongs to the direct real-semigroup dependency, and endpoint
and localization-error holomorphy to the separate endpoints node. -/
def node_stationary_u2D_analytic_u2D_semigroupStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    (∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      HasSmoothBounds D Q →
      let i : Fin d := ⟨0, by omega⟩
      let F := forcedComplexEvolution Q i
      let Fdag := fun ζ t => complexL2Transpose (reducedLaw Q) (F ζ t)
      (∀ ζ : ℂ, IsComplexEnvironmentSemigroup Q i ζ (F ζ) ∧
        IsComplexTransposeSemigroup Q (F ζ) (Fdag ζ)) ∧
      (∀ (t : ℝ≥0) (ζ : ℂ),
        AnalyticAt ℂ (fun z => F z t) ζ ∧ AnalyticAt ℂ (fun z => Fdag z t) ζ) ∧
      (∀ (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) (ζ : ℂ),
        AnalyticAt ℂ (fun z => ∫ r in Icc (0 : ℝ) (t : ℝ), F z r.toNNReal f) ζ ∧
        AnalyticAt ℂ (fun z => ∫ r in Icc (0 : ℝ) (t : ℝ), Fdag z r.toNNReal f) ζ)) ∧
    ∀ (p R T : ℝ) (hp : 2 ≤ p), 0 < R → 0 < T →
      letI : Fact (1 ≤ ENNReal.ofReal p) :=
        ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
      ∃ C : ℝ, 0 < C ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
        HasSmoothBounds D Q →
        let i : Fin d := ⟨0, by omega⟩
        let F := forcedComplexEvolution Q i
        let Fdag := fun ζ t => complexL2Transpose (reducedLaw Q) (F ζ t)
        ∀ f : Lp ℂ 2 (reducedLaw Q), MemLp f (ENNReal.ofReal p) (reducedLaw Q) →
        ∀ t : ℝ≥0, (t : ℝ) ≤ T →
          (∀ ζ : ℂ, ‖ζ‖ ≤ R →
            MemLp (F ζ t f) (ENNReal.ofReal p) (reducedLaw Q) ∧
            MemLp (Fdag ζ t f) (ENNReal.ofReal p) (reducedLaw Q) ∧
            eLpNorm (F ζ t f) (ENNReal.ofReal p) (reducedLaw Q) ≤
              ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) (reducedLaw Q) ∧
            eLpNorm (Fdag ζ t f) (ENNReal.ofReal p) (reducedLaw Q) ≤
              ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) (reducedLaw Q)) ∧
          ∃ u udag : ℂ → Lp ℂ (ENNReal.ofReal p) (reducedLaw Q),
            (∀ ζ : ℂ, (u ζ : FieldPair d → ℂ) =ᵐ[reducedLaw Q] F ζ t f ∧
              (udag ζ : FieldPair d → ℂ) =ᵐ[reducedLaw Q] Fdag ζ t f) ∧
            ∀ ζ : ℂ, AnalyticAt ℂ u ζ ∧ AnalyticAt ℂ udag ζ

end EinsteinFull.Blueprint
