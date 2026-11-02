import EinsteinFull.Frozen.ReducedLawStationary
import EinsteinFull.Frozen.ComplexHorizontalGradient

open MeasureTheory
open scoped BigOperators

namespace EinsteinFull

open EinsteinRelation

/-- The full `L²` graph of `L_ζ = (1/2) D·aD + ζ a e_i·D`, defined by its
bilinear weak form on the actual horizontal `H¹` space of the reduced law.
No generator, derivative, semigroup, or estimate is selected by this predicate. -/
def IsComplexGeneratorPair {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ)
    (f g : Lp ℂ 2 (reducedLaw Q)) : Prop :=
  ∃ Gf : Fin d → Lp ℂ 2 (reducedLaw Q),
    HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f Gf ∧
    ∀ (v : Lp ℂ 2 (reducedLaw Q)) (Gv : Fin d → Lp ℂ 2 (reducedLaw Q)),
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) v Gv →
      (∫ ω, g ω * v ω ∂reducedLaw Q) =
        -(1 / 2 : ℂ) * (∫ ω,
          ∑ j, ∑ k, (ω.1 0 j k : ℂ) * Gf k ω * Gv j ω ∂reducedLaw Q) +
        ζ * (∫ ω, (∑ j, (ω.1 0 j i : ℂ) * Gf j ω) * v ω ∂reducedLaw Q)

end EinsteinFull
