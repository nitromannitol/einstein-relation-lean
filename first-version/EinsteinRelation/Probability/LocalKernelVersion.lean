import EinsteinRelation.Regeneration.Coupling
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.Integral
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# A local kernel from local scalar integral versions

Source `paper/main.tex:383–387,413`: the extension from path tests to joint
path and local-environment tests. Conditional averaging constructs a
single local version of a finite kernel from the individual local
versions of its bounded scalar integrals.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace EinsteinRelation.Probability

/-- Individual local versions of bounded kernel integrals determine a
single local kernel version, simultaneously on all measurable sets. -/
theorem exists_local_kernel_of_local_integral_versions
    {α β : Type*} [mα : MeasurableSpace α] [MeasurableSpace β]
    [StandardBorelSpace α] [MeasurableSpace.CountableOrCountablyGenerated α β]
    (μ : Measure α) [IsFiniteMeasure μ] (κ : Kernel α β) [IsFiniteKernel κ]
    (m : MeasurableSpace α) (hm : m ≤ mα)
    (hlocal : ∀ F : β → ℝ, Measurable F → Regeneration.BoundedRealTest F →
      ∃ A : α → ℝ, Measurable[m] A ∧ A =ᵐ[μ] fun a => ∫ b, F b ∂κ a) :
    ∃ η : @Kernel α β m inferInstance,
      IsFiniteKernel η ∧ ∀ᵐ a ∂μ, κ a = η a := by
  classical
  letI : MeasurableSpace α := mα
  let η : @Kernel α β m inferInstance := κ ∘ₖ condExpKernel μ m
  let η' : Kernel α β := η.comap id (measurable_id.mono le_rfl hm)
  have heq : ∀ t : Set β, MeasurableSet t →
      (fun a => (κ a).real t) =ᵐ[μ] fun a => (η' a).real t := by
    intro t ht
    obtain ⟨A, hA, hAe⟩ := hlocal (t.indicator (fun _ => 1))
      (measurable_const.indicator ht) ⟨1, fun b => by by_cases hb : b ∈ t <;> simp [hb]⟩
    simp only [integral_indicator ht, setIntegral_one_eq_measureReal] at hAe
    have hfi := Kernel.IsFiniteKernel.integrable μ κ ht
    have hfm : AEStronglyMeasurable[m] (fun a => (κ a).real t) μ :=
      hA.stronglyMeasurable.aestronglyMeasurable.congr hAe
    have hc := condExp_ae_eq_integral_condExpKernel hm hfi
    have hf := condExp_of_aestronglyMeasurable' hm hfm hfi
    have hi : ∀ a, (η' a).real t =
        ∫ b, (κ b).real t ∂condExpKernel μ m a := by
      intro a
      have h := Kernel.integral_comp (η := κ) (κ := condExpKernel μ m) (a := a)
        ((integrable_const (1 : ℝ)).indicator ht)
      simpa only [integral_indicator ht, setIntegral_one_eq_measureReal] using h
    filter_upwards [hc, hf] with a ha hfa
    rw [hi, ← ha, hfa]
  have heq' : ∀ t : Set β, MeasurableSet t →
      (fun a => κ a t) =ᵐ[μ] fun a => η' a t := by
    intro t ht
    filter_upwards [heq t ht] with a ha
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top (κ a) t)
      (measure_ne_top (η' a) t)).mp ha
  have hprod : μ.compProd κ = μ.compProd η' := by
    apply Measure.ext_prod
    intro s t hs ht
    rw [Measure.compProd_apply_prod hs ht, Measure.compProd_apply_prod hs ht]
    exact setLIntegral_congr_fun_ae hs ((heq' t ht).mono fun _ h _ => h)
  refine ⟨η, inferInstance, ?_⟩
  exact Kernel.ae_eq_of_compProd_eq hprod


end EinsteinRelation.Probability
