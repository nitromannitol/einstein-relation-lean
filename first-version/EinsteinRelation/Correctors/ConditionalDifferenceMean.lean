import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! Conditional mean of a difference of two conditionally independent copies.

Source: `corrector.conditional` Step 4, paper/main.tex:886–890. For an integrable
`EuclideanSpace ℝ ι`-valued `f` and a measurable observation `X`, the second copy `f a'` is drawn
from the regular conditional law `condDistrib id X Q (X a)` of the coefficient given the
observation. Its mean is the conditional expectation `Q[f | σ(X)] a`, so the conditional mean of
`f a - f a'` is the centered variable `f a - Q[f | σ(X)] a`. This is the identity
`Z¹ - E[Z¹ | F] = E[Z¹ - Z² | a₁]` used in that step.

The proof uses Mathlib's `condExp_ae_eq_integral_condDistrib_id` for the conditional mean and
the disintegration `compProd_map_condDistrib` for fiber integrability. It assumes no
independence of `Q` from `X`, no global measurability of `f`, and no standard Borel structure
beyond the one `condDistrib` requires on `A`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace EinsteinRelation.Correctors

/-- For integrable `f`, the regular conditional law of the coefficient given `X` is integrable for
`Q`-almost every observation. The joint law `(Q.map X) ⊗ₘ condDistrib id X Q` is the image of `Q`
under `a ↦ (X a, a)`, so `f` is integrable on it. Its fiber integrability over `Q.map X` then pulls
back to `Q` through `X`. -/
private theorem ae_integrable_condDistrib_id {A B E : Type*} [MeasurableSpace A]
    [StandardBorelSpace A] [Nonempty A] [MeasurableSpace B] [NormedAddCommGroup E]
    (Q : Measure A) [IsProbabilityMeasure Q] (X : A → B) (hX : Measurable X) {f : A → E}
    (hf : Integrable f Q) :
    ∀ᵐ a ∂Q, Integrable f (condDistrib (id : A → A) X Q (X a)) := by
  have hid : AEMeasurable (id : A → A) Q := measurable_id.aemeasurable
  have hjoint : Integrable (fun z : B × A => f z.2)
      ((Q.map X) ⊗ₘ condDistrib (id : A → A) X Q) := by
    rw [compProd_map_condDistrib hid]
    exact hf.comp_snd_map_prodMk X
  have hfiber : ∀ᵐ b ∂(Q.map X), Integrable f (condDistrib (id : A → A) X Q b) :=
    ((Measure.integrable_compProd_iff hjoint.aestronglyMeasurable).mp hjoint).1
  exact ae_of_ae_map (p := fun b => Integrable f (condDistrib (id : A → A) X Q b))
    hX.aemeasurable hfiber

/-- Source: `corrector.conditional` Step 4, paper/main.tex:886–890.

For every integrable `EuclideanSpace ℝ ι`-valued `f` and every measurable observation `X`, the
conditional mean of `f a - f a'` over the second copy `a' ∼ condDistrib id X Q (X a)` equals the
centered variable `f a - Q[f | σ(X)] a`, for `Q`-almost every `a`. The index type `ι` is an
arbitrary finite type. -/
theorem ae_conditional_difference_mean (ι : Type) [Fintype ι] {A B : Type}
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A] [MeasurableSpace B]
    (Q : Measure A) [IsProbabilityMeasure Q] (X : A → B) (hX : Measurable X)
    {f : A → EuclideanSpace ℝ ι} (hf : Integrable f Q) :
    ∀ᵐ a ∂Q, (∫ a', f a - f a' ∂condDistrib (id : A → A) X Q (X a)) =
      f a - Q[f | (inferInstance : MeasurableSpace B).comap X] a := by
  have hce : Q[f | (inferInstance : MeasurableSpace B).comap X] =ᵐ[Q]
      fun a => ∫ y, f y ∂condDistrib (id : A → A) X Q (X a) :=
    condExp_ae_eq_integral_condDistrib_id hX hf
  filter_upwards [hce, ae_integrable_condDistrib_id Q X hX hf] with a ha hfa
  have hconst : Integrable (fun _ : A => f a) (condDistrib (id : A → A) X Q (X a)) :=
    integrable_const (f a)
  rw [ha, integral_sub hconst hfa, integral_const, probReal_univ, one_smul]

end EinsteinRelation.Correctors
