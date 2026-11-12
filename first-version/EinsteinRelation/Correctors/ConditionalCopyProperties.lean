import EinsteinRelation.Correctors.ConditionalCopyMarginals
import EinsteinRelation.Correctors.ConditionalFiber
import EinsteinRelation.Correctors.CopyObservationAgreement
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Composition.Prod

/-! The composed conditional-copy law.

Source: `corrector.conditional` Step 4, paper/main.tex:886–894, and the local-corrector
conditioning at paper/main.tex:947–963. The coupling `P` is the literal conditional-product law
`(Q.map X) ⊗ₘ (K ×ₖ K)` with `K = condDistrib id X Q`. It is a probability measure, both of its
copy coordinates have marginal `Q`, and the two copies agree in their observation almost surely.
Each conjunct is taken from a checked helper; no external hypothesis is assumed.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace EinsteinRelation.Correctors

/-- The conditional-copy law `P = (Q.map X) ⊗ₘ (K ×ₖ K)` with `K = condDistrib id X Q` is a
probability measure, both copy marginals equal `Q`, and the two copies share their observation
almost surely. The law is the actual conditional product, not an existential coupling. -/
theorem conditionalCopy_properties {A B : Type} [MeasurableSpace A] [StandardBorelSpace A]
    [Nonempty A] [MeasurableSpace B] [StandardBorelSpace B]
    (Q : Measure A) [IsProbabilityMeasure Q] (X : A → B) (hX : Measurable X) :
    let P := (Q.map X) ⊗ₘ (condDistrib (id : A → A) X Q ×ₖ condDistrib (id : A → A) X Q)
    IsProbabilityMeasure P ∧ P.map (fun z : B × (A × A) => z.2.1) = Q ∧
      P.map (fun z : B × (A × A) => z.2.2) = Q ∧
      ∀ᵐ z ∂P, X z.2.1 = X z.2.2 := by
  dsimp only
  have hprob : IsProbabilityMeasure (Q.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  obtain ⟨hfst, hsnd⟩ := conditionalCopy_marginals Q X hX
  refine ⟨inferInstance, hfst, hsnd, ?_⟩
  exact ae_copy_observation_eq (Q.map X) (condDistrib (id : A → A) X Q) X hX
    (condDistrib_ae_fiber Q X hX)

end EinsteinRelation.Correctors
