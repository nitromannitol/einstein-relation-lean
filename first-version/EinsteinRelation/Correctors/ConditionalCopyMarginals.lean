import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.MeasureTheory.Measure.Map

/-! Marginals of the conditional-product copies law.

Source: `corrector.conditional` Step 4, paper/main.tex:886–894. The joint law
`(Q.map X) ⊗ₘ (K ×ₖ K)` with `K = condDistrib id X Q` places two conditionally
independent copies of the coefficient carrier over the observation `X`. Each copy
has marginal `Q`. The proof uses Mathlib kernel and measure identities only. It
assumes neither independence of `Q` nor any coupling agreement, and it needs no
standard Borel structure on `B`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace EinsteinRelation.Correctors

/-- Projecting the second copy of `μ ⊗ₘ (κ ×ₖ κ)` through `Prod.map id Prod.fst` recovers
`μ ⊗ₘ κ`: the first projection of a product kernel is the original kernel. -/
private theorem compProd_prod_map_fst {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure B} [SFinite μ] {κ : Kernel B A} [IsMarkovKernel κ] :
    (μ ⊗ₘ (κ ×ₖ κ)).map (Prod.map id Prod.fst) = μ ⊗ₘ κ := by
  rw [← Measure.compProd_map (measurable_fst : Measurable (Prod.fst : A × A → A)),
    ← Kernel.fst_eq, Kernel.fst_prod]

/-- Projecting the third coordinate of `μ ⊗ₘ (κ ×ₖ κ)` through `Prod.map id Prod.snd` recovers
`μ ⊗ₘ κ`: the second projection of a product kernel is the second factor. -/
private theorem compProd_prod_map_snd {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure B} [SFinite μ] {κ : Kernel B A} [IsMarkovKernel κ] :
    (μ ⊗ₘ (κ ×ₖ κ)).map (Prod.map id Prod.snd) = μ ⊗ₘ κ := by
  rw [← Measure.compProd_map (measurable_snd : Measurable (Prod.snd : A × A → A)),
    ← Kernel.snd_eq, Kernel.snd_prod]

/-- The base conditional law `(Q.map X) ⊗ₘ condDistrib id X Q` has second marginal `Q`.
This is the disintegration of the joint law of `(X, id)` under `Q`. -/
private theorem map_snd_compProd_condDistrib {A B : Type*} [MeasurableSpace A]
    [StandardBorelSpace A] [Nonempty A] [MeasurableSpace B] (Q : Measure A)
    [IsProbabilityMeasure Q] {X : A → B} (hX : Measurable X) :
    ((Q.map X) ⊗ₘ condDistrib (id : A → A) X Q).map (Prod.snd : B × A → A) = Q := by
  have hid : AEMeasurable (id : A → A) Q := measurable_id.aemeasurable
  rw [compProd_map_condDistrib hid,
    Measure.map_map (measurable_snd : Measurable (Prod.snd : B × A → A))
      (hX.prodMk measurable_id)]
  exact Measure.map_id

/-- Both `A`-marginals of the conditional-product copies law equal `Q`. The first
conjunct uses the first copy coordinate `z.2.1`, the second conjunct uses `z.2.2`. -/
theorem conditionalCopy_marginals {A B : Type*} [MeasurableSpace A] [StandardBorelSpace A]
    [Nonempty A] [MeasurableSpace B] (Q : Measure A) [IsProbabilityMeasure Q] (X : A → B)
    (hX : Measurable X) :
    (((Q.map X) ⊗ₘ (condDistrib (id : A → A) X Q ×ₖ condDistrib (id : A → A) X Q)).map
      (fun z : B × (A × A) => z.2.1)) = Q ∧
    (((Q.map X) ⊗ₘ (condDistrib (id : A → A) X Q ×ₖ condDistrib (id : A → A) X Q)).map
      (fun z : B × (A × A) => z.2.2)) = Q := by
  have hfst : Measurable (Prod.map id Prod.fst : B × (A × A) → B × A) :=
    measurable_id.prodMap measurable_fst
  have hsnd : Measurable (Prod.map id Prod.snd : B × (A × A) → B × A) :=
    measurable_id.prodMap measurable_snd
  have hsndA : Measurable (Prod.snd : B × A → A) := measurable_snd
  constructor
  · calc
      ((Q.map X) ⊗ₘ (condDistrib (id : A → A) X Q ×ₖ condDistrib (id : A → A) X Q)).map
          (fun z : B × (A × A) => z.2.1)
        = ((((Q.map X) ⊗ₘ (condDistrib (id : A → A) X Q ×ₖ condDistrib (id : A → A) X Q)).map
            (Prod.map id Prod.fst)).map Prod.snd) :=
          (Measure.map_map hsndA hfst).symm
      _ = ((Q.map X) ⊗ₘ condDistrib (id : A → A) X Q).map Prod.snd := by
          rw [compProd_prod_map_fst]
      _ = Q := map_snd_compProd_condDistrib Q hX
  · calc
      ((Q.map X) ⊗ₘ (condDistrib (id : A → A) X Q ×ₖ condDistrib (id : A → A) X Q)).map
          (fun z : B × (A × A) => z.2.2)
        = ((((Q.map X) ⊗ₘ (condDistrib (id : A → A) X Q ×ₖ condDistrib (id : A → A) X Q)).map
            (Prod.map id Prod.snd)).map Prod.snd) :=
          (Measure.map_map hsndA hsnd).symm
      _ = ((Q.map X) ⊗ₘ condDistrib (id : A → A) X Q).map Prod.snd := by
          rw [compProd_prod_map_snd]
      _ = Q := map_snd_compProd_condDistrib Q hX

end EinsteinRelation.Correctors
