import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-! Concentration of the actual conditional distribution on its observation fiber.

This is the fiber step of `corrector.conditional` Step 4, paper/main.tex:886–894. For a
measurable observation `X : A → B` of the canonical coefficient carrier `A`, the regular
conditional distribution `condDistrib id X Q b` of the coefficient given `X = b` is concentrated
on `{a | X a = b}`, for almost every `b` under the law `Q.map X`.

The proof uses Mathlib only. The joint law of `(X, id)` is the marginal of `X` composed with
`condDistrib id X Q` (`compProd_map_condDistrib`). The graph predicate `X a = b` is measurable on
`B × A` because a standard Borel space has a measurable diagonal. The almost-everywhere statement
then passes from the joint law to the fibers (`Measure.ae_ae_of_ae_compProd`). No coupling,
marginal, or independence hypothesis is assumed.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace EinsteinRelation.Correctors

/-- The diagonal of a standard Borel space is measurable. A compatible Polish topology makes the
diagonal closed and provides the metrizable and second countable structure behind `MeasurableEq`. -/
private theorem measurableSet_diagonal_std (B : Type*) [MeasurableSpace B]
    [StandardBorelSpace B] : MeasurableSet (Set.diagonal B) := by
  obtain ⟨_, _, _⟩ := (inferInstance : StandardBorelSpace B).polish
  exact measurableSet_diagonal

/-- The actual conditional distribution of the coefficient given its observation is concentrated
on the observation fiber: for almost every observed value `b` (under `Q.map X`), almost every
coefficient `a` drawn from `condDistrib id X Q b` satisfies `X a = b`. -/
theorem condDistrib_ae_fiber {A B : Type*} [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
    [MeasurableSpace B] [StandardBorelSpace B] (Q : Measure A) [IsProbabilityMeasure Q]
    (X : A → B) (hX : Measurable X) :
    ∀ᵐ b ∂(Q.map X), ∀ᵐ a ∂(condDistrib (id : A → A) X Q b), X a = b := by
  -- The joint law of `(X, id)` is the marginal of `X` composed with the conditional kernel.
  have hpair : Measurable (fun a : A => (X a, id a)) := hX.prodMk measurable_id
  have hcomp : (Q.map X) ⊗ₘ condDistrib (id : A → A) X Q = Q.map (fun a => (X a, id a)) :=
    compProd_map_condDistrib measurable_id.aemeasurable
  -- The graph predicate `X z.2 = z.1` on `B × A` is the preimage of the diagonal of `B`.
  have hf : Measurable (fun z : B × A => (X z.2, z.1)) :=
    (hX.comp measurable_snd).prodMk measurable_fst
  have hS : MeasurableSet {z : B × A | X z.2 = z.1} := by
    have hdiag : MeasurableSet (Set.diagonal B) := measurableSet_diagonal_std B
    exact hf hdiag
  -- Pull the predicate back through the joint law; it holds identically on the graph of `X`.
  have hae : ∀ᵐ z ∂((Q.map X) ⊗ₘ condDistrib (id : A → A) X Q), X z.2 = z.1 := by
    rw [hcomp]
    exact (MeasureTheory.ae_map_iff hpair.aemeasurable hS).mpr
      (Filter.Eventually.of_forall fun a => rfl)
  -- Pass from the joint law to the conditional fibers.
  exact Measure.ae_ae_of_ae_compProd hae

end EinsteinRelation.Correctors
