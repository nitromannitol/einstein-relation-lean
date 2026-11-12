import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.MeasurableSpace.Basic

/-! Conditional expectation transported along a measurable map to its image law.

Source: `paper/main.tex:886–891`, Step 4 of the proof of the local corrector bound, where the
coefficient-law conditional expectations are carried to the physical probability space by a
measurable map. For a probability measure `Q` on `A`, a measurable `Y : A → B`, and a measurable
`X : B → C`, the conditional expectation of `f ∘ Y` given the σ-algebra `comap (X ∘ Y)` is,
`Q`-almost everywhere, the composition with `Y` of the conditional expectation of `f` given
`comap X` under the image law `Q.map Y`.

The proof uses the uniqueness characterization `ae_eq_condExp_of_forall_setIntegral_eq`. Every set
of `comap (X ∘ Y)` is a preimage `Y ⁻¹' T` with `T` in `comap X`, and set integrals are moved
between `Q` and `Q.map Y` by `setIntegral_map`. No standard Borel structure, independence, or
assumed conditional-expectation conclusion enters.
-/

open MeasureTheory
open scoped ENNReal

namespace EinsteinRelation.Correctors

/-- Conditional expectation along a measurable map is the image-law conditional expectation
composed with that map.

Source: `paper/main.tex:886–891`. For a probability measure `Q` on `A`, measurable `Y : A → B`,
measurable `X : B → C`, and a measurable integrable `f : B → ℝ` under `Q.map Y`, the conditional
expectation of `f ∘ Y` given `comap (X ∘ Y)` agrees `Q`-almost everywhere with
`(Q.map Y)[f | comap X] ∘ Y`. -/
theorem condExp_comap_comp_map {A B C : Type} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] (Q : Measure A) [IsProbabilityMeasure Q]
    (Y : A → B) (hY : Measurable Y) (X : B → C) (hX : Measurable X)
    {f : B → ℝ} (hf : Measurable f) (hfint : Integrable f (Q.map Y)) :
    Q[(fun a => f (Y a)) | (inferInstance : MeasurableSpace C).comap (X ∘ Y)] =ᵐ[Q]
      (fun a => (Q.map Y)[f | (inferInstance : MeasurableSpace C).comap X] (Y a)) := by
  -- Inclusions of the two sub-σ-algebras, from the measurability of `X ∘ Y` and of `X`.
  have hXY : (inferInstance : MeasurableSpace C).comap (X ∘ Y) ≤
      (inferInstance : MeasurableSpace A) :=
    (hX.comp hY).comap_le
  have hXB : (inferInstance : MeasurableSpace C).comap X ≤
      (inferInstance : MeasurableSpace B) :=
    hX.comap_le
  -- The image law is a probability measure, so its conditional expectations are available.
  haveI : IsProbabilityMeasure (Q.map Y) := Measure.isProbabilityMeasure_map hY.aemeasurable
  -- Every measurable set of `comap (X ∘ Y)` is `Y ⁻¹' T` for some `T` measurable in `comap X`.
  have hsplit : ∀ s : Set A, MeasurableSet[(inferInstance : MeasurableSpace C).comap (X ∘ Y)] s →
      ∃ T : Set B, MeasurableSet[(inferInstance : MeasurableSpace C).comap X] T ∧ Y ⁻¹' T = s := by
    intro s hs
    obtain ⟨S, hS, rfl⟩ := MeasurableSpace.measurableSet_comap.1 hs
    exact ⟨X ⁻¹' S, MeasurableSpace.measurableSet_comap.2 ⟨S, hS, rfl⟩, rfl⟩
  -- `Y` is measurable from `comap (X ∘ Y)` to `comap X`.
  have hYm : @Measurable A B ((inferInstance : MeasurableSpace C).comap (X ∘ Y))
      ((inferInstance : MeasurableSpace C).comap X) Y := by
    intro T hT
    obtain ⟨S, hS, rfl⟩ := MeasurableSpace.measurableSet_comap.1 hT
    exact MeasurableSpace.measurableSet_comap.2 ⟨S, hS, rfl⟩
  -- The conditional expectation of `f` is `comap X`-measurable, hence its composition with `Y` is
  -- `comap (X ∘ Y)`-measurable.
  have hh : @Measurable B ℝ ((inferInstance : MeasurableSpace C).comap X) inferInstance
      ((Q.map Y)[f | (inferInstance : MeasurableSpace C).comap X]) :=
    stronglyMeasurable_condExp.measurable
  have hgmeas : @Measurable A ℝ ((inferInstance : MeasurableSpace C).comap (X ∘ Y)) inferInstance
      (fun a => (Q.map Y)[f | (inferInstance : MeasurableSpace C).comap X] (Y a)) :=
    hh.comp hYm
  -- Integrability under the image law, and transfer to `Q` along `Y`.
  have hfAE : AEStronglyMeasurable f (Q.map Y) := hf.aestronglyMeasurable
  have hhint : Integrable ((Q.map Y)[f | (inferInstance : MeasurableSpace C).comap X]) (Q.map Y) :=
    integrable_condExp
  have hhAE : AEStronglyMeasurable ((Q.map Y)[f | (inferInstance : MeasurableSpace C).comap X])
      (Q.map Y) :=
    hhint.aestronglyMeasurable
  have hYae : AEMeasurable Y Q := hY.aemeasurable
  have hfQ : Integrable (fun a => f (Y a)) Q := hfint.comp_measurable hY
  have hgint : Integrable
      (fun a => (Q.map Y)[f | (inferInstance : MeasurableSpace C).comap X] (Y a)) Q :=
    hhint.comp_measurable hY
  -- Set integrals over `comap (X ∘ Y)` agree: move each set to the image law, use the
  -- conditional expectation identity there, and move back.
  have hgEq : ∀ s : Set A, MeasurableSet[(inferInstance : MeasurableSpace C).comap (X ∘ Y)] s →
      Q s < ∞ →
      (∫ a in s, (Q.map Y)[f | (inferInstance : MeasurableSpace C).comap X] (Y a) ∂Q) =
        ∫ a in s, f (Y a) ∂Q := by
    intro s hs _
    obtain ⟨T, hT, rfl⟩ := hsplit s hs
    have hTB : MeasurableSet T := hXB T hT
    exact (setIntegral_map hTB hhAE hYae).symm.trans
      ((setIntegral_condExp hXB hfint hT).trans (setIntegral_map hTB hfAE hYae))
  -- Uniqueness of the conditional expectation identifies the candidate `Q`-almost everywhere.
  exact (ae_eq_condExp_of_forall_setIntegral_eq hXY hfQ (fun s _ _ => hgint.integrableOn)
    hgEq hgmeas.aestronglyMeasurable).symm

end EinsteinRelation.Correctors
