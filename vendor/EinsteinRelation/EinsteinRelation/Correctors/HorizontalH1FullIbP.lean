import EinsteinRelation.Calculus.HorizontalSobolev
import EinsteinRelation.Correctors.HorizontalGeneratorsIbP

/-! # Full-domain integration by parts on the horizontal H¹ domain

Source `eq.horizontal-ibp`, `paper/main.tex:240–248`, with its uses in the Step 2 commutator and
time-averaging argument at `paper/main.tex:545–566`. For `f, g` in the actual horizontal H¹ domain
`horizontalH1` and the canonical coordinate gradient `horizontalH1Gradient`, the products
`(∂ᵢf) g` and `f (∂ᵢg)` are integrable and `E[(∂ᵢf) g] = -E[f (∂ᵢg)]`.

The proof consumes only the strong L² generator characterization
`hasHorizontalLpDerivative_horizontalH1Gradient` and the full-domain pair integration by parts
`horizontalGenerators_integration_by_parts`. No smooth-core, graph-density or integration-by-parts
premise is assumed.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

/-- Source `eq.horizontal-ibp`, `paper/main.tex:240–248`: for `f, g` in the actual horizontal H¹
domain and a coordinate `i`, the products of the canonical gradient of `f` with `g` and of `f` with
the canonical gradient of `g` are integrable, and `E[(∂ᵢf) g] = -E[f (∂ᵢg)]`. -/
theorem horizontalH1_integration_by_parts {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) (f g : horizontalH1 Q hQ) (i : Fin d) :
    Integrable (fun ω => (horizontalH1Gradient Q hQ f i) ω * (g : Lp ℝ 2 Q) ω) Q ∧
    Integrable (fun ω => (f : Lp ℝ 2 Q) ω * (horizontalH1Gradient Q hQ g i) ω) Q ∧
    (∫ ω, (horizontalH1Gradient Q hQ f i) ω * (g : Lp ℝ 2 Q) ω ∂Q) =
      -(∫ ω, (f : Lp ℝ 2 Q) ω * (horizontalH1Gradient Q hQ g i) ω ∂Q) :=
  horizontalGenerators_integration_by_parts Q hQ i (f : Lp ℝ 2 Q) (horizontalH1Gradient Q hQ f i)
    (g : Lp ℝ 2 Q) (horizontalH1Gradient Q hQ g i)
    (hasHorizontalLpDerivative_horizontalH1Gradient Q hQ f i)
    (hasHorizontalLpDerivative_horizontalH1Gradient Q hQ g i)

end EinsteinRelation.Correctors
