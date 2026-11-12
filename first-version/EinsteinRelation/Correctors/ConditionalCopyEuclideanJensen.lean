import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.MeasurableIntegral
import EinsteinRelation.Correctors.ConditionalDifferenceMean

/-! Conditional Jensen step for the copy-difference corrector, with Euclidean (`L²`) norms.

Source: `corrector.conditional` Step 4 applied to the `EuclideanSpace ℝ ι`-valued gradient,
paper/main.tex:886–894. For `Q`-almost every `a`, the centered variable `f a - Q[f | σ(X)] a` is the
average of `f a - f a'` over the second copy `a' ∼ K (X a)`, where `K = condDistrib id X Q`
(`ae_conditional_difference_mean`). Averaging contracts finite-`p` norms (Jensen for kernels). The
averaged integrand is then transported to the conditional-copy law `(Q.map X) ⊗ₘ (K ×ₖ K)` by two
identities: the base law `(Q.map X) ⊗ₘ K` is the image of `Q` under `a ↦ (X a, a)`, and
`compProd_assoc'` reassociates `((Q.map X) ⊗ₘ K) ⊗ₘ (K ∘ fst)` to `(Q.map X) ⊗ₘ (K ×ₖ K)`.

No independence of `Q` from `X` is assumed, and no standard Borel structure on `B` is needed. The
norm is the Euclidean one of `EuclideanSpace ℝ ι`; no supremum-norm or constant is used.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace EinsteinRelation.Correctors

/-- Probability averaging of an `EuclideanSpace ℝ ι`-valued function is bounded by its finite-p
seminorm. -/
private theorem enorm_integral_le_eLpNorm_copy {ι : Type*} [Fintype ι] {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {p : ℝ≥0∞} (hp : 1 ≤ p)
    {f : Ω → EuclideanSpace ℝ ι} (hf : AEStronglyMeasurable f μ) :
    ‖∫ a, f a ∂μ‖ₑ ≤ eLpNorm f p μ := by
  calc
    ‖∫ a, f a ∂μ‖ₑ ≤ ∫⁻ a, ‖f a‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
    _ = eLpNorm f 1 μ := (eLpNorm_one_eq_lintegral_enorm).symm
    _ ≤ eLpNorm f p μ := eLpNorm_le_eLpNorm_of_exponent_le hp hf

/-- A kernel average of an `EuclideanSpace ℝ ι`-valued integrand contracts finite-p seminorms on
the base law `μ` with the joint law `μ ⊗ₘ κ`, for an arbitrary finite index type `ι`. -/
private theorem eLpNorm_kernel_average_copy {ι : Type*} [Fintype ι] {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} [SFinite μ] (κ : Kernel α β)
    [IsMarkovKernel κ] {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    {g : α × β → EuclideanSpace ℝ ι} (hg : Measurable g) :
    eLpNorm (fun a => ∫ b, g (a, b) ∂κ a) p μ ≤ eLpNorm g p (μ ⊗ₘ κ) := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp_top
  rw [eLpNorm_eq_lintegral_rpow_enorm hp0 hp_top,
    eLpNorm_eq_lintegral_rpow_enorm hp0 hp_top]
  refine ENNReal.rpow_le_rpow ?_ (le_of_lt (one_div_pos.mpr hpr))
  rw [Measure.lintegral_compProd (hg.enorm.pow_const p.toReal)]
  apply lintegral_mono
  intro a
  calc
    ‖∫ b, g (a, b) ∂κ a‖ₑ ^ p.toReal ≤
        (eLpNorm (fun b => g (a, b)) p (κ a)) ^ p.toReal :=
      ENNReal.rpow_le_rpow (enorm_integral_le_eLpNorm_copy (ι := ι) hp
        ((hg.comp (measurable_prodMk_left (x := a))).stronglyMeasurable.aestronglyMeasurable))
        hpr.le
    _ = ∫⁻ b, ‖g (a, b)‖ₑ ^ p.toReal ∂κ a := by
      rw [eLpNorm_eq_eLpNorm' hp0 hp_top]
      exact (lintegral_rpow_enorm_eq_rpow_eLpNorm' hpr).symm

/-- The product kernel of a Markov kernel with itself is the composition-product of that kernel
with its first-coordinate comap: both copies are drawn from `K` at the same point. Both sides
evaluate to `∫⁻ x, K b (Prod.mk x ⁻¹' s) ∂(K b)`. -/
private theorem prod_kernel_eq_compProd_comap_fst {A B : Type*} [MeasurableSpace A]
    [MeasurableSpace B] (K : Kernel B A) [IsMarkovKernel K] :
    K ×ₖ K = K ⊗ₖ (K.comap Prod.fst measurable_fst) := by
  refine Kernel.ext fun b => Measure.ext fun s hs => ?_
  exact (Kernel.prod_apply' K K b hs).trans
    (Kernel.compProd_apply hs K (K.comap Prod.fst measurable_fst) b).symm

/-- Reassociation of the two conditionally independent copies: the iterated composition-product
`((μ ⊗ₘ K) ⊗ₘ (K ∘ fst))` over `(B × A) × A` pushes forward under `MeasurableEquiv.prodAssoc` to
the product-kernel law `μ ⊗ₘ (K ×ₖ K)` over `B × (A × A)`. -/
private theorem map_prodAssoc_compProd_comap_fst {A B : Type*} [MeasurableSpace A]
    [MeasurableSpace B] (μ : Measure B) (K : Kernel B A) [IsMarkovKernel K] :
    ((μ ⊗ₘ K) ⊗ₘ (K.comap Prod.fst measurable_fst)).map MeasurableEquiv.prodAssoc =
      μ ⊗ₘ (K ×ₖ K) := by
  rw [Measure.compProd_assoc', prod_kernel_eq_compProd_comap_fst K]

/-- Source: `corrector.conditional` Step 4 applied to Euclidean-valued gradients,
paper/main.tex:886–894.

For every integrable, measurable `EuclideanSpace ℝ ι`-valued `f` and every measurable observation
`X`, the Euclidean `L^p` error of the conditional mean is bounded by the `L^p` norm of the copy
difference `f z.2.1 - f z.2.2` on the conditional-copy law `(Q.map X) ⊗ₘ (K ×ₖ K)`, where
`K = condDistrib id X Q`. The exponent `p` is finite and at least one. The index type `ι` is
arbitrary and finite. -/
theorem eLpNorm_conditional_error_piL2_le_copy_difference (ι : Type) [Fintype ι] {A B : Type}
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A] [MeasurableSpace B] (Q : Measure A)
    [IsProbabilityMeasure Q] (X : A → B) (hX : Measurable X) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hpt : p ≠ ∞) {f : A → EuclideanSpace ℝ ι} (hfm : Measurable f) (hf : Integrable f Q) :
    eLpNorm (f - Q[f | (inferInstance : MeasurableSpace B).comap X]) p Q ≤
      eLpNorm (fun z : B × (A × A) => f z.2.1 - f z.2.2) p
        ((Q.map X) ⊗ₘ (condDistrib (id : A → A) X Q ×ₖ condDistrib (id : A → A) X Q)) := by
  have hid : AEMeasurable (id : A → A) Q := measurable_id.aemeasurable
  have hF : Measurable (fun a : A => (X a, id a)) := hX.prodMk measurable_id
  -- Centered variable as the average of the copy difference over the second copy (Q-a.e.).
  have hcen : (f - Q[f | (inferInstance : MeasurableSpace B).comap X]) =ᵐ[Q]
      fun a => ∫ y, f a - f y ∂(condDistrib (id : A → A) X Q (X a)) := by
    filter_upwards [ae_conditional_difference_mean ι Q X hX hf] with a ha
    rw [Pi.sub_apply, ha]
  -- The base law `(Q.map X) ⊗ₘ K` is the law of `a ↦ (X a, a)` under `Q`.
  have hM0 : (Q.map X) ⊗ₘ condDistrib (id : A → A) X Q =
      Q.map (fun a : A => (X a, id a)) :=
    compProd_map_condDistrib hid
  have hg2 : Measurable (fun v : (B × A) × A => f v.1.2 - f v.2) :=
    (hfm.comp (measurable_snd.comp measurable_fst)).sub (hfm.comp measurable_snd)
  have hG : Measurable (fun z : B × (A × A) => f z.2.1 - f z.2.2) :=
    (hfm.comp (measurable_fst.comp measurable_snd)).sub
      (hfm.comp (measurable_snd.comp measurable_snd))
  -- Fiberwise average of the second copy, measurable in the base point.
  have hh : StronglyMeasurable
      (fun z : B × A => ∫ y, f z.2 - f y ∂(condDistrib (id : A → A) X Q z.1)) :=
    hg2.stronglyMeasurable.integral_kernel_prod_right'
      (κ := ((condDistrib (id : A → A) X Q).comap Prod.fst measurable_fst : Kernel (B × A) A))
  -- Kernel averaging of the second copy over the base law `(Q.map X) ⊗ₘ K`.
  have hav : eLpNorm (fun z : B × A => ∫ y, f z.2 - f y ∂(condDistrib (id : A → A) X Q z.1)) p
      ((Q.map X) ⊗ₘ condDistrib (id : A → A) X Q) ≤
      eLpNorm (fun v : (B × A) × A => f v.1.2 - f v.2) p
        (((Q.map X) ⊗ₘ condDistrib (id : A → A) X Q) ⊗ₘ
          (condDistrib (id : A → A) X Q).comap Prod.fst measurable_fst) :=
    eLpNorm_kernel_average_copy (ι := ι)
      (μ := (Q.map X) ⊗ₘ condDistrib (id : A → A) X Q)
      (κ := (condDistrib (id : A → A) X Q).comap Prod.fst measurable_fst)
      (p := p) (g := fun v : (B × A) × A => f v.1.2 - f v.2) hp hpt hg2
  -- Left side: the base-law average is the `Q`-average of the centered variable.
  have hLHS : eLpNorm (fun z : B × A => ∫ y, f z.2 - f y ∂(condDistrib (id : A → A) X Q z.1)) p
      ((Q.map X) ⊗ₘ condDistrib (id : A → A) X Q) =
      eLpNorm (fun a : A => ∫ y, f a - f y ∂(condDistrib (id : A → A) X Q (X a))) p Q := by
    rw [hM0]
    exact eLpNorm_map_measure hh.aestronglyMeasurable hF.aemeasurable
  -- Right side: reassociate the two copies to the conditional-copy law.
  have hRHS : eLpNorm (fun z : B × (A × A) => f z.2.1 - f z.2.2) p
      ((Q.map X) ⊗ₘ (condDistrib (id : A → A) X Q ×ₖ condDistrib (id : A → A) X Q)) =
      eLpNorm (fun v : (B × A) × A => f v.1.2 - f v.2) p
        (((Q.map X) ⊗ₘ condDistrib (id : A → A) X Q) ⊗ₘ
          (condDistrib (id : A → A) X Q).comap Prod.fst measurable_fst) := by
    rw [← map_prodAssoc_compProd_comap_fst (Q.map X) (condDistrib (id : A → A) X Q)]
    exact eLpNorm_map_measure hG.aestronglyMeasurable
      (MeasurableEquiv.measurable MeasurableEquiv.prodAssoc).aemeasurable
  calc eLpNorm (f - Q[f | (inferInstance : MeasurableSpace B).comap X]) p Q
      = eLpNorm (fun a : A => ∫ y, f a - f y ∂(condDistrib (id : A → A) X Q (X a))) p Q :=
        eLpNorm_congr_ae hcen
    _ = eLpNorm (fun z : B × A => ∫ y, f z.2 - f y ∂(condDistrib (id : A → A) X Q z.1)) p
        ((Q.map X) ⊗ₘ condDistrib (id : A → A) X Q) := hLHS.symm
    _ ≤ eLpNorm (fun v : (B × A) × A => f v.1.2 - f v.2) p
        (((Q.map X) ⊗ₘ condDistrib (id : A → A) X Q) ⊗ₘ
          (condDistrib (id : A → A) X Q).comap Prod.fst measurable_fst) := hav
    _ = eLpNorm (fun z : B × (A × A) => f z.2.1 - f z.2.2) p
        ((Q.map X) ⊗ₘ (condDistrib (id : A → A) X Q ×ₖ condDistrib (id : A → A) X Q)) :=
        hRHS.symm

end EinsteinRelation.Correctors
