import EinsteinFull.Frozen.ComplexGeneratorGraph

open MeasureTheory Filter
open scoped Topology NNReal

namespace EinsteinFull

open EinsteinRelation

/-- The `C₀` semigroup of the paper's complex generator, specified by equality
of its complete infinitesimal-generator graph with the actual weak-form graph.
This predicate includes no force analyticity, growth estimate, decay estimate,
locality, corrector, covariance, or response conclusion. -/
def IsComplexEnvironmentSemigroup {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ)
    (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)) : Prop :=
  P 0 = ContinuousLinearMap.id ℂ (Lp ℂ 2 (reducedLaw Q)) ∧
  (∀ s t : ℝ≥0, P (s + t) = (P s).comp (P t)) ∧
  (∀ f : Lp ℂ 2 (reducedLaw Q), Continuous (fun t : ℝ≥0 => P t f)) ∧
  ∀ f g : Lp ℂ 2 (reducedLaw Q),
    Tendsto (fun t : ℝ≥0 => ((t : ℝ) : ℂ)⁻¹ • (P t f - f))
      (𝓝[>] (0 : ℝ≥0)) (𝓝 g) ↔ IsComplexGeneratorPair Q i ζ f g

end EinsteinFull
