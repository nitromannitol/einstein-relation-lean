import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# Conditional expectation under a pushforward

For a measurable map `f`, the conditional expectation of `g` under `P.map f` given `m₀`,
composed with `f`, is the conditional expectation of `g ∘ f` under `P` given the pullback
`m₀.comap f`.
-/

open MeasureTheory

namespace EinsteinFull

variable {Ω Ω₀ E : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem condExp_map_comp {m₀ : MeasurableSpace Ω₀} [mΩ₀ : MeasurableSpace Ω₀] {P : Measure Ω}
    [IsFiniteMeasure P] {f : Ω → Ω₀} (hf : Measurable f) (hm₀ : m₀ ≤ mΩ₀) {g : Ω₀ → E}
    (hg : Integrable g (P.map f)) :
    (fun ω => ((P.map f)[g | m₀]) (f ω)) =ᵐ[P] P[g ∘ f | m₀.comap f] := by
  have hm : m₀.comap f ≤ mΩ := (MeasurableSpace.comap_mono hm₀).trans hf.comap_le
  have hfm : Measurable[m₀.comap f, m₀] f := comap_measurable f
  have hsm : StronglyMeasurable[m₀] ((P.map f)[g | m₀]) := stronglyMeasurable_condExp
  have hint_c : Integrable ((P.map f)[g | m₀]) (P.map f) := integrable_condExp
  have hcomp : Integrable (fun ω => ((P.map f)[g | m₀]) (f ω)) P :=
    (integrable_map_measure (hsm.mono hm₀).aestronglyMeasurable hf.aemeasurable).1 hint_c
  have hgf : Integrable (g ∘ f) P :=
    (integrable_map_measure hg.aestronglyMeasurable hf.aemeasurable).1 hg
  refine ae_eq_condExp_of_forall_setIntegral_eq hm hgf ?_ ?_ ?_
  · intro s _ _
    exact hcomp.integrableOn
  · intro s hs _
    obtain ⟨t, ht, rfl⟩ := hs
    have ht' : MeasurableSet t := hm₀ t ht
    rw [← setIntegral_map ht' (hsm.mono hm₀).aestronglyMeasurable hf.aemeasurable,
      setIntegral_condExp hm₀ hg ht,
      setIntegral_map ht' hg.aestronglyMeasurable hf.aemeasurable]
    rfl
  · exact (hsm.comp_measurable hfm).aestronglyMeasurable

end EinsteinFull
