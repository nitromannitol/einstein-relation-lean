import EinsteinRelation.Correctors.KernelLpContraction
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.MeasurableIntegral

/-! Conditional Jensen comparison for the conditional-product copies law.

Source: `corrector.conditional` Step 4, paper/main.tex:886–894, and the conditioning in
`corrector.local`, paper/main.tex:948–973. For `K = condDistrib id X Q` the copies law is
`P = (Q.map X) ⊗ₘ (K ×ₖ K)`. The conditional error `f - Q[f | σ(X)]` is the average over the
second copy of `f a1 - f a2` under the fiber `K (X a1)`. Scalar kernel averaging
(`eLpNorm_kernel_integral_le`) then bounds it by the copy difference in `L^p(P)`.

The proof uses only Mathlib kernel and measure identities, the conditional-mean identity
`condExp_ae_eq_integral_condDistrib_id`, and the checked scalar averaging lemma. It assumes no
independence, no coupling agreement, and no Jensen conclusion. The measurability of `f` is the
source regularity premise. The second-copy kernel is `K.comap Prod.fst` on the base `B × A`, and
the iterated composition `((Q.map X) ⊗ₘ K) ⊗ₘ (K.comap Prod.fst)` is reassociated to `P`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace EinsteinRelation.Correctors

/-- The product kernel `K ×ₖ K` is the composition `K ⊗ₖ (K ∘ fst)`: the second factor is `K`
evaluated at the first coordinate, which is the same kernel in the second copy. -/
private theorem prod_eq_compProd_comap_fst {A B : Type*} [MeasurableSpace A]
    [MeasurableSpace B] (K : Kernel B A) [IsMarkovKernel K] :
    K ×ₖ K = K ⊗ₖ (K.comap (Prod.fst : B × A → B) measurable_fst) := by
  refine Kernel.ext fun b => Measure.ext fun s hs => ?_
  exact (Kernel.prod_apply' K K b hs).trans
    (Kernel.compProd_apply hs K (K.comap (Prod.fst : B × A → B) measurable_fst) b).symm

/-- Reassociating the iterated composition `(μ ⊗ₘ K) ⊗ₘ (K ∘ fst)` through
`MeasurableEquiv.prodAssoc` gives the product-kernel triple law `μ ⊗ₘ (K ×ₖ K)`. -/
private theorem compProd_comap_fst_map_prodAssoc {A B : Type*} [MeasurableSpace A]
    [MeasurableSpace B] (μ : Measure B) (K : Kernel B A) [IsMarkovKernel K] :
    ((μ ⊗ₘ K) ⊗ₘ (K.comap (Prod.fst : B × A → B) measurable_fst)).map
        MeasurableEquiv.prodAssoc =
      μ ⊗ₘ (K ×ₖ K) := by
  rw [Measure.compProd_assoc', prod_eq_compProd_comap_fst K]

/-- Fiberwise copy averaging for an arbitrary Markov kernel `K : Kernel B A`. With first-copy
joint law `μ0 ⊗ₘ K`, the second copy is the kernel `K.comap Prod.fst` on `B × A`, and the
averaged integrand `w ↦ ∫ y, f w.2 - f y` is bounded in `L^p(μ0 ⊗ₘ K)` by the copy difference
in `L^p(μ0 ⊗ₘ (K ×ₖ K))`. Only `SFinite μ0` is used, to apply the kernel averaging lemma. -/
private theorem eLpNorm_fiber_copy_difference_le {A B : Type*} [MeasurableSpace A]
    [MeasurableSpace B] (μ0 : Measure B) [SFinite μ0] (K : Kernel B A) [IsMarkovKernel K]
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞) {f : A → ℝ} (hf : Measurable f) :
    eLpNorm (fun w : B × A => ∫ y, (f w.2 - f y) ∂(K w.1)) p (μ0 ⊗ₘ K) ≤
    eLpNorm (fun z : B × (A × A) => f z.2.1 - f z.2.2) p (μ0 ⊗ₘ (K ×ₖ K)) := by
  -- The copy difference `f a1 - f a2` on the triple `((b, a1), a2)` and on `(b, (a1, a2))`.
  have hFsm : StronglyMeasurable (fun v : (B × A) × A => f v.1.2 - f v.2) :=
    ((hf.comp (measurable_snd.comp measurable_fst)).sub (hf.comp measurable_snd)).stronglyMeasurable
  have hgm : Measurable (fun z : B × (A × A) => f z.2.1 - f z.2.2) :=
    (hf.comp (measurable_fst.comp measurable_snd)).sub
      (hf.comp (measurable_snd.comp measurable_snd))
  -- Scalar averaging over the second copy contracts the `L^p` norm. The integrand uses `K w.1`,
  -- which is definitionally `(K.comap Prod.fst _) w` (`Kernel.comap_apply`); the `comap` form
  -- inside a lambda leaves the `MeasurableSpace` argument of `Kernel.comap` unresolved.
  have havg : eLpNorm (fun w : B × A => ∫ y, (f w.2 - f y) ∂(K w.1)) p (μ0 ⊗ₘ K) ≤
      eLpNorm (fun v : (B × A) × A => f v.1.2 - f v.2) p
        ((μ0 ⊗ₘ K) ⊗ₘ (K.comap (Prod.fst : B × A → B) measurable_fst)) :=
    eLpNorm_kernel_integral_le (μ := μ0 ⊗ₘ K) (p := p)
      (f := fun v : (B × A) × A => f v.1.2 - f v.2)
      (K.comap (Prod.fst : B × A → B) measurable_fst) hp hpt hFsm
  -- Reassociation identifies the triple-product law with `μ0 ⊗ₘ (K ×ₖ K)`.
  have hassoc : ((μ0 ⊗ₘ K) ⊗ₘ (K.comap (Prod.fst : B × A → B) measurable_fst)).map
      MeasurableEquiv.prodAssoc = μ0 ⊗ₘ (K ×ₖ K) :=
    compProd_comap_fst_map_prodAssoc μ0 K
  have hpa : Measurable (⇑(MeasurableEquiv.prodAssoc : ((B × A) × A) ≃ᵐ B × A × A)) :=
    MeasurableEquiv.measurable _
  have hrhs : eLpNorm (fun v : (B × A) × A => f v.1.2 - f v.2) p
        ((μ0 ⊗ₘ K) ⊗ₘ (K.comap (Prod.fst : B × A → B) measurable_fst)) =
      eLpNorm (fun z : B × (A × A) => f z.2.1 - f z.2.2) p (μ0 ⊗ₘ (K ×ₖ K)) := by
    rw [← hassoc]
    exact (eLpNorm_map_measure
      (μ := (μ0 ⊗ₘ K) ⊗ₘ (K.comap (Prod.fst : B × A → B) measurable_fst))
      (f := ⇑(MeasurableEquiv.prodAssoc : ((B × A) × A) ≃ᵐ B × A × A))
      (g := fun z : B × (A × A) => f z.2.1 - f z.2.2) (p := p)
      hgm.aestronglyMeasurable hpa.aemeasurable).symm
  exact havg.trans_eq hrhs

/-- Conditional Jensen comparison for the actual conditional-product copies law. The `L^p(Q)`
error of conditioning `f` on `X` is at most the `L^p(P)` norm of the copy difference
`f a1 - f a2`, where `P = (Q.map X) ⊗ₘ (K ×ₖ K)` and `K = condDistrib id X Q`. -/
theorem eLpNorm_conditional_error_le_copy_difference {A B : Type} [MeasurableSpace A]
    [StandardBorelSpace A] [Nonempty A] [MeasurableSpace B] (Q : Measure A)
    [IsProbabilityMeasure Q] (X : A → B) (hX : Measurable X) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hpt : p ≠ ∞) {f : A → ℝ} (hf : Measurable f) (hfi : Integrable f Q) :
    eLpNorm (f - Q[f | (inferInstance : MeasurableSpace B).comap X]) p Q ≤
    eLpNorm (fun z : B × (A × A) => f z.2.1 - f z.2.2) p
      ((Q.map X) ⊗ₘ (condDistrib (id : A → A) X Q ×ₖ condDistrib (id : A → A) X Q)) := by
  haveI : IsProbabilityMeasure (Q.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  -- The first copy's base law is `Q.map X`; the coupling `(Q.map X) ⊗ₘ K` is the law of
  -- `(X, id)` under `Q`.
  have hcomp : (Q.map X) ⊗ₘ condDistrib (id : A → A) X Q = Q.map (fun a => (X a, id a)) :=
    compProd_map_condDistrib measurable_id.aemeasurable
  -- Fiber integrability of `f` comes from the genuine disintegration of `Integrable f Q`.
  have hjoint : Integrable (fun z : B × A => f z.2)
      ((Q.map X) ⊗ₘ condDistrib (id : A → A) X Q) := by
    rw [hcomp]
    exact hfi.comp_snd_map_prodMk X
  have hfib : ∀ᵐ b ∂(Q.map X), Integrable f (condDistrib (id : A → A) X Q b) :=
    ((Measure.integrable_compProd_iff hjoint.aestronglyMeasurable).mp hjoint).1
  have hfibQ : ∀ᵐ a ∂Q, Integrable f (condDistrib (id : A → A) X Q (X a)) :=
    ae_of_ae_map (p := fun b => Integrable f (condDistrib (id : A → A) X Q b))
      hX.aemeasurable hfib
  -- The conditional mean is the fiber average of `f` under `K`.
  have hce : Q[f | (inferInstance : MeasurableSpace B).comap X] =ᵐ[Q]
      fun a => ∫ y, f y ∂(condDistrib (id : A → A) X Q (X a)) :=
    condExp_ae_eq_integral_condDistrib_id hX hfi
  -- The conditional error is the fiber average of `f a - f a2` over the second copy.
  have hlhs : (f - Q[f | (inferInstance : MeasurableSpace B).comap X]) =ᵐ[Q]
      fun a => ∫ a2, (f a - f a2) ∂(condDistrib (id : A → A) X Q (X a)) := by
    filter_upwards [hce, hfibQ] with a ha hai
    have hint : Integrable (fun _ : A => f a) (condDistrib (id : A → A) X Q (X a)) :=
      integrable_const (f a)
    rw [integral_sub hint hai, integral_const, Pi.sub_apply, ha]
    simp
  -- Measurability of the second-copy integrand and of its fiber average.
  have hFsm : StronglyMeasurable (fun v : (B × A) × A => f v.1.2 - f v.2) :=
    ((hf.comp (measurable_snd.comp measurable_fst)).sub (hf.comp measurable_snd)).stronglyMeasurable
  have hGsm : StronglyMeasurable (fun w : B × A => ∫ y, (f w.2 - f y)
        ∂(condDistrib (id : A → A) X Q w.1)) :=
    hFsm.integral_kernel_prod_right'
      (κ := (condDistrib (id : A → A) X Q).comap (Prod.fst : B × A → B) measurable_fst)
  have hψ : Measurable (fun a => (X a, id a)) := hX.prodMk measurable_id
  -- Change of variables from `Q` to the coupling `Q.map (X, id) = (Q.map X) ⊗ₘ K`.
  have hmap : eLpNorm (fun a => ∫ a2, (f a - f a2) ∂(condDistrib (id : A → A) X Q (X a))) p Q =
      eLpNorm (fun w : B × A => ∫ y, (f w.2 - f y) ∂(condDistrib (id : A → A) X Q w.1))
        p ((Q.map X) ⊗ₘ condDistrib (id : A → A) X Q) := by
    rw [hcomp]
    exact (eLpNorm_map_measure (μ := Q) (f := fun a => (X a, id a))
      (g := fun w : B × A => ∫ y, (f w.2 - f y) ∂(condDistrib (id : A → A) X Q w.1))
      (p := p) hGsm.aestronglyMeasurable hψ.aemeasurable).symm
  exact (eLpNorm_congr_ae (p := p) hlhs).trans_le (hmap.trans_le
    (eLpNorm_fiber_copy_difference_le (Q.map X) (condDistrib (id : A → A) X Q) hp hpt hf))

end EinsteinRelation.Correctors
