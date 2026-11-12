import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Composition.Prod

/-! Almost-sure agreement of observations for the literal conditional-product copies.

This is the coupling step of `corrector.conditional`, paper/main.tex:886–894: two copies of the
coefficient field that are conditionally independent given the observation agree on that
observation. Here the observation is `X : A → B` with `B` standard Borel, the conditional law of
the coefficient given its observation is the kernel `κ : Kernel B A`, and the two copies are drawn
from the literal product `κ ×ₖ κ`. The local conditioning that consumes this coupling is at
paper/main.tex:948–973.

The hypothesis `hfiber` is the per-fiber fact for `condDistrib id X Q`, whose producer is the
ConditionalFiber step. It is an argument of this internal kernel lemma, not an external input.
No independence of the original law is asserted. The two copies are independent only inside the
product `κ ×ₖ κ`.
-/

open MeasureTheory ProbabilityTheory

namespace EinsteinRelation.Correctors

/-- The diagonal of a standard Borel space is measurable. A measurable embedding into `ℝ` is
injective, so the diagonal is the preimage of the equality set of `ℝ` under it. -/
private lemma measurableSet_diagonal_standardBorel (B : Type*) [MeasurableSpace B]
    [StandardBorelSpace B] : MeasurableSet {p : B × B | p.1 = p.2} := by
  obtain ⟨f, hf⟩ := MeasureTheory.exists_measurableEmbedding_real B
  have hset : {p : B × B | p.1 = p.2} = {p : B × B | f p.1 = f p.2} := by
    ext p
    simp only [Set.mem_setOf_eq]
    exact ⟨fun h => congrArg f h, fun h => hf.injective h⟩
  rw [hset]
  exact measurableSet_eq_fun (hf.measurable.comp measurable_fst)
    (hf.measurable.comp measurable_snd)

/-- Two copies of the coefficient field drawn from the literal conditional product `κ ×ₖ κ`
agree in their observation almost surely.

Given the observation `b`, the two copies are independent draws from `κ b`. The hypothesis
`hfiber` says that each draw lies on the fiber `X ⁻¹' {b}` almost surely, so the pair agrees
almost surely under the product `κ b ⊗ κ b`. The composition-product with `ν` then lifts this
fiberwise statement to the joint triple law. -/
theorem ae_copy_observation_eq {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [StandardBorelSpace B]
    (ν : Measure B) [SFinite ν] (κ : Kernel B A) [IsMarkovKernel κ] (X : A → B) (hX : Measurable X)
    (hfiber : ∀ᵐ b ∂ν, ∀ᵐ a ∂κ b, X a = b) :
    ∀ᵐ z ∂(ν ⊗ₘ (κ ×ₖ κ)), X z.2.1 = X z.2.2 := by
  -- Agreement of the observations of two points is a measurable event on `A × A`.
  have hpair : MeasurableSet {w : A × A | X w.1 = X w.2} :=
    (measurableSet_diagonal_standardBorel B).preimage
      ((hX.comp measurable_fst).prodMk (hX.comp measurable_snd))
  -- On each fiber, two independent copies from `κ b` agree, since both equal `b` almost surely.
  have hfib : ∀ᵐ b ∂ν, ∀ᵐ c ∂((κ ×ₖ κ) b), X c.1 = X c.2 := by
    filter_upwards [hfiber] with b hb
    rw [Kernel.prod_apply κ κ b]
    refine (Measure.ae_prod_iff_ae_ae hpair).2 ?_
    filter_upwards [hb] with a₁ ha₁
    filter_upwards [hb] with a₂ ha₂
    exact ha₁.trans ha₂.symm
  -- The agreement event is measurable on the triple space, so the composition-product lifts it.
  have hall : MeasurableSet {z : B × (A × A) | X z.2.1 = X z.2.2} :=
    hpair.preimage measurable_snd
  exact Measure.ae_compProd_of_ae_ae (p := fun z : B × (A × A) => X z.2.1 = X z.2.2) hall hfib

end EinsteinRelation.Correctors
